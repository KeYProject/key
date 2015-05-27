package org.key_project.javaeditor.outline;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.CompletionRequestor;
import org.eclipse.jdt.core.IBuffer;
import org.eclipse.jdt.core.IBufferFactory;
import org.eclipse.jdt.core.ICodeCompletionRequestor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.ICompletionRequestor;
import org.eclipse.jdt.core.IImportContainer;
import org.eclipse.jdt.core.IImportDeclaration;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.WorkingCopyOwner;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.text.edits.TextEdit;
import org.eclipse.text.edits.UndoEdit;

/**
 * Wraps an {@link ICompilationUnit} to change the content in the outline.
 * @author Martin Hentschel
 */
@SuppressWarnings("deprecation")
public class OutlineCompilationUnitWrapper extends OutlineJavaElementWrapper<ICompilationUnit> implements ICompilationUnit {
   /**
    * Constructor.
    * @param wrappedObject The wrapped {@link ICompilationUnit}.
    */
   public OutlineCompilationUnitWrapper(ICompilationUnit wrappedObject) {
      super(wrappedObject);
   }

   @Override
   public IJavaElement[] getChildren() throws JavaModelException {
      // TODO: Define an extension point and API to extend and modify the children shown in the oultine. Realize the extension point for JML in plug-in org.key_project.jmlediting.ui.
      IJavaElement[] children = getWrappedObject().getChildren();
      return children.length >= 1 ?
             new IJavaElement[] {children[0]} :
             children;
   }

   @Override
   public boolean hasChildren() throws JavaModelException {
      return getWrappedObject().hasChildren();
   }

   @Override
   public IType findPrimaryType() {
      return getWrappedObject().findPrimaryType();
   }

   @Override
   public IJavaElement getElementAt(int position) throws JavaModelException {
      return getWrappedObject().getElementAt(position);
   }

   @Override
   public ICompilationUnit getWorkingCopy(WorkingCopyOwner owner, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().getWorkingCopy(owner, monitor);
   }

   @Override
   public void close() throws JavaModelException {
      getWrappedObject().close();
   }

   @Override
   public String findRecommendedLineSeparator() throws JavaModelException {
      return getWrappedObject().findRecommendedLineSeparator();
   }

   @Override
   public IBuffer getBuffer() throws JavaModelException {
      return getWrappedObject().getBuffer();
   }

   @Override
   public boolean hasUnsavedChanges() throws JavaModelException {
      return getWrappedObject().hasUnsavedChanges();
   }

   @Override
   public boolean isConsistent() throws JavaModelException {
      return getWrappedObject().isConsistent();
   }

   @Override
   public boolean isOpen() {
      return getWrappedObject().isOpen();
   }

   @Override
   public void makeConsistent(IProgressMonitor progress) throws JavaModelException {
      getWrappedObject().makeConsistent(progress);
   }

   @Override
   public void open(IProgressMonitor progress) throws JavaModelException {
      getWrappedObject().open(progress);
   }

   @Override
   public void save(IProgressMonitor progress, boolean force) throws JavaModelException {
      getWrappedObject().save(progress, force);
   }

   @Override
   public String getSource() throws JavaModelException {
      return getWrappedObject().getSource();
   }

   @Override
   public ISourceRange getSourceRange() throws JavaModelException {
      return getWrappedObject().getSourceRange();
   }

   @Override
   public ISourceRange getNameRange() throws JavaModelException {
      return getWrappedObject().getNameRange();
   }

   @Override
   public void codeComplete(int offset, ICodeCompletionRequestor requestor) throws JavaModelException {
      getWrappedObject().codeComplete(offset, requestor);
   }

   @Override
   public void codeComplete(int offset, ICompletionRequestor requestor) throws JavaModelException {
      getWrappedObject().codeComplete(offset, requestor);
   }

   @Override
   public void codeComplete(int offset, CompletionRequestor requestor) throws JavaModelException {
      getWrappedObject().codeComplete(offset, requestor);
   }

   @Override
   public void codeComplete(int offset, CompletionRequestor requestor, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().codeComplete(offset, requestor, monitor);
   }

   @Override
   public void codeComplete(int offset, ICompletionRequestor requestor, WorkingCopyOwner owner) throws JavaModelException {
      getWrappedObject().codeComplete(offset, requestor, owner);
   }

   @Override
   public void codeComplete(int offset, CompletionRequestor requestor, WorkingCopyOwner owner) throws JavaModelException {
      getWrappedObject().codeComplete(offset, requestor, owner);
   }

   @Override
   public void codeComplete(int offset, CompletionRequestor requestor, WorkingCopyOwner owner, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().codeComplete(offset, requestor, owner, monitor);
   }

   @Override
   public IJavaElement[] codeSelect(int offset, int length) throws JavaModelException {
      return getWrappedObject().codeSelect(offset, length);
   }

   @Override
   public IJavaElement[] codeSelect(int offset, int length, WorkingCopyOwner owner) throws JavaModelException {
      return getWrappedObject().codeSelect(offset, length, owner);
   }

   @Override
   public void commit(boolean force, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().commit(force, monitor);
   }

   @Override
   public void destroy() {
      getWrappedObject().destroy();
   }

   @Override
   public IJavaElement findSharedWorkingCopy(IBufferFactory bufferFactory) {
      return getWrappedObject().findSharedWorkingCopy(bufferFactory);
   }

   @Override
   public IJavaElement getOriginal(IJavaElement workingCopyElement) {
      return getWrappedObject().getOriginal(workingCopyElement);
   }

   @Override
   public IJavaElement getOriginalElement() {
      return getWrappedObject().getOriginalElement();
   }

   @Override
   public IJavaElement getSharedWorkingCopy(IProgressMonitor monitor, IBufferFactory factory, IProblemRequestor problemRequestor) throws JavaModelException {
      return getWrappedObject().getSharedWorkingCopy(monitor, factory, problemRequestor);
   }

   @Override
   public IJavaElement getWorkingCopy() throws JavaModelException {
      return getWrappedObject().getWorkingCopy();
   }

   @Override
   public IJavaElement getWorkingCopy(IProgressMonitor monitor, IBufferFactory factory, IProblemRequestor problemRequestor) throws JavaModelException {
      return getWrappedObject().getWorkingCopy(monitor, factory, problemRequestor);
   }

   @Override
   public boolean isBasedOn(IResource resource) {
      return getWrappedObject().isBasedOn(resource);
   }

   @Override
   public IMarker[] reconcile() throws JavaModelException {
      return getWrappedObject().reconcile();
   }

   @Override
   public void reconcile(boolean forceProblemDetection, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().reconcile(forceProblemDetection, monitor);
   }

   @Override
   public void copy(IJavaElement container, IJavaElement sibling, String rename, boolean replace, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().copy(container, sibling, rename, replace, monitor);
   }

   @Override
   public void delete(boolean force, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().delete(force, monitor);
   }

   @Override
   public void move(IJavaElement container, IJavaElement sibling, String rename, boolean replace, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().move(container, sibling, rename, replace, monitor);
   }

   @Override
   public void rename(String name, boolean replace, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().rename(name, replace, monitor);
   }

   @Override
   public UndoEdit applyTextEdit(TextEdit edit, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().applyTextEdit(edit, monitor);
   }

   @Override
   public void becomeWorkingCopy(IProblemRequestor problemRequestor, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().becomeWorkingCopy(problemRequestor, monitor);
   }

   @Override
   public void becomeWorkingCopy(IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().becomeWorkingCopy(monitor);
   }

   @Override
   public void commitWorkingCopy(boolean force, IProgressMonitor monitor) throws JavaModelException {
      getWrappedObject().commit(force, monitor);
   }

   @Override
   public IImportDeclaration createImport(String name, IJavaElement sibling, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().createImport(name, sibling, monitor);
   }

   @Override
   public IImportDeclaration createImport(String name, IJavaElement sibling, int flags, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().createImport(name, sibling, flags, monitor);
   }

   @Override
   public IPackageDeclaration createPackageDeclaration(String name, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().createPackageDeclaration(name, monitor);
   }

   @Override
   public IType createType(String contents, IJavaElement sibling, boolean force, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().createType(contents, sibling, force, monitor);
   }

   @Override
   public void discardWorkingCopy() throws JavaModelException {
      getWrappedObject().discardWorkingCopy();
   }

   @Override
   public IJavaElement[] findElements(IJavaElement element) {
      return getWrappedObject().findElements(element);
   }

   @Override
   public ICompilationUnit findWorkingCopy(WorkingCopyOwner owner) {
      return getWrappedObject().findWorkingCopy(owner);
   }

   @Override
   public IType[] getAllTypes() throws JavaModelException {
      return getWrappedObject().getAllTypes();
   }

   @Override
   public IImportDeclaration getImport(String name) {
      return getWrappedObject().getImport(name);
   }

   @Override
   public IImportContainer getImportContainer() {
      return getWrappedObject().getImportContainer();
   }

   @Override
   public IImportDeclaration[] getImports() throws JavaModelException {
      return getWrappedObject().getImports();
   }

   @Override
   public ICompilationUnit getPrimary() {
      return getWrappedObject().getPrimary();
   }

   @Override
   public WorkingCopyOwner getOwner() {
      return getWrappedObject().getOwner();
   }

   @Override
   public IPackageDeclaration getPackageDeclaration(String name) {
      return getWrappedObject().getPackageDeclaration(name);
   }

   @Override
   public IPackageDeclaration[] getPackageDeclarations() throws JavaModelException {
      return getWrappedObject().getPackageDeclarations();
   }

   @Override
   public IType getType(String name) {
      return getWrappedObject().getType(name);
   }

   @Override
   public IType[] getTypes() throws JavaModelException {
      return getWrappedObject().getTypes();
   }

   @Override
   public ICompilationUnit getWorkingCopy(IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().getWorkingCopy(monitor);
   }

   @Override
   public ICompilationUnit getWorkingCopy(WorkingCopyOwner owner, IProblemRequestor problemRequestor, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().getWorkingCopy(owner, problemRequestor, monitor);
   }

   @Override
   public boolean hasResourceChanged() {
      return getWrappedObject().hasResourceChanged();
   }

   @Override
   public boolean isWorkingCopy() {
      return getWrappedObject().isWorkingCopy();
   }

   @Override
   public CompilationUnit reconcile(int astLevel, boolean forceProblemDetection, WorkingCopyOwner owner, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().reconcile(astLevel, forceProblemDetection, owner, monitor);
   }

   @Override
   public CompilationUnit reconcile(int astLevel, boolean forceProblemDetection, boolean enableStatementsRecovery, WorkingCopyOwner owner, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().reconcile(astLevel, forceProblemDetection, enableStatementsRecovery, owner, monitor);
   }

   @Override
   public CompilationUnit reconcile(int astLevel, int reconcileFlags, WorkingCopyOwner owner, IProgressMonitor monitor) throws JavaModelException {
      return getWrappedObject().reconcile(astLevel, reconcileFlags, owner, monitor);
   }

   @Override
   public void restore() throws JavaModelException {
      getWrappedObject().restore();
   }
}