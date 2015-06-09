package org.key_project.javaeditor.outline;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaModel;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IOpenable;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.ISourceReference;
import org.eclipse.jdt.core.JavaModelException;

/**
 * General implementation of {@link IOutlineWrapper} for {@link IJavaElement}s.
 * @author Martin Hentschel
 * @param <J> The type of the wrapped {@link IJavaElement}.
 */
public class OutlineJavaElementWrapper<J extends IJavaElement> implements IJavaElement, ISourceReference, IOutlineWrapper<J> {
   /**
    * The wrapped {@link IJavaElement}.
    */
   private J wrappedObject;

   /**
    * Constructor.
    * @param wrappedObject The wrapped {@link IJavaElement}.
    */
   public OutlineJavaElementWrapper(J wrappedObject) {
      this.wrappedObject = wrappedObject;
   }

   @Override
   public J getWrappedObject() {
      return wrappedObject;
   }

   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class adapter) {
      return wrappedObject.getAdapter(adapter);
   }

   @Override
   public boolean exists() {
      return wrappedObject.exists();
   }

   @Override
   public IJavaElement getAncestor(int ancestorType) {
      return wrappedObject.getAncestor(ancestorType);
   }

   @Override
   public String getAttachedJavadoc(IProgressMonitor monitor)throws JavaModelException {
      return wrappedObject.getAttachedJavadoc(monitor);
   }

   @Override
   public IResource getCorrespondingResource() throws JavaModelException {
      return wrappedObject.getCorrespondingResource();
   }

   @Override
   public String getElementName() {
      return wrappedObject.getElementName();
   }

   @Override
   public int getElementType() {
      return wrappedObject.getElementType();
   }

   @Override
   public String getHandleIdentifier() {
      return wrappedObject.getHandleIdentifier();
   }

   @Override
   public IJavaModel getJavaModel() {
      return wrappedObject.getJavaModel();
   }

   @Override
   public IJavaProject getJavaProject() {
      return wrappedObject.getJavaProject();
   }

   @Override
   public IOpenable getOpenable() {
      return wrappedObject.getOpenable();
   }

   @Override
   public IJavaElement getParent() {
      return wrappedObject.getParent();
   }

   @Override
   public IPath getPath() {
      return wrappedObject.getPath();
   }

   @Override
   public IJavaElement getPrimaryElement() {
      return wrappedObject.getPrimaryElement();
   }

   @Override
   public IResource getResource() {
      return wrappedObject.getResource();
   }

   @Override
   public ISchedulingRule getSchedulingRule() {
      return wrappedObject.getSchedulingRule();
   }

   @Override
   public IResource getUnderlyingResource() throws JavaModelException {
      return wrappedObject.getUnderlyingResource();
   }

   @Override
   public boolean isReadOnly() {
      return wrappedObject.isReadOnly();
   }

   @Override
   public boolean isStructureKnown() throws JavaModelException {
      return wrappedObject.isStructureKnown();
   }

   @Override
   public String getSource() throws JavaModelException {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public ISourceRange getSourceRange() throws JavaModelException {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public ISourceRange getNameRange() throws JavaModelException {
      // TODO Auto-generated method stub
      return null;
   }

}
