package org.key_project.jmlediting.ui.outlineView;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaModel;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IOpenable;
import org.eclipse.jdt.core.JavaModelException;

public class JMLCommentOutlineElement implements IJavaElement {

   private IJavaElement parent;

   public JMLCommentOutlineElement(IJavaElement parent) {
      this.parent = parent;
   }
   
   @Override
   public Object getAdapter(Class adapter) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public boolean exists() {
      // TODO Auto-generated method stub
      return false;
   }

   @Override
   public IJavaElement getAncestor(int ancestorType) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public String getAttachedJavadoc(IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IResource getCorrespondingResource() throws JavaModelException {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public String getElementName() {
      return "JML Comment";
   }

   @Override
   public int getElementType() {
      return IJavaElement.FIELD;
   }

   @Override
   public String getHandleIdentifier() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IJavaModel getJavaModel() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IJavaProject getJavaProject() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IOpenable getOpenable() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IJavaElement getParent() {
      return parent;
   }

   @Override
   public IPath getPath() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IJavaElement getPrimaryElement() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IResource getResource() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public ISchedulingRule getSchedulingRule() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IResource getUnderlyingResource() throws JavaModelException {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public boolean isReadOnly() {
      // TODO Auto-generated method stub
      return false;
   }

   @Override
   public boolean isStructureKnown() throws JavaModelException {
      // TODO Auto-generated method stub
      return false;
   }

}
