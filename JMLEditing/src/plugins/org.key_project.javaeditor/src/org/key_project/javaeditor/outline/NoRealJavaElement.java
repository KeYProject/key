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
import org.eclipse.jdt.core.JavaModelException;

public class NoRealJavaElement implements IJavaElement {
   private final IJavaProject javaProject;
   
   private final String elementName;
   
   public NoRealJavaElement(IJavaProject javaProject, String elementName) {
      this.javaProject = javaProject;
      this.elementName = elementName;
   }

   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class adapter) {
      return Platform.getAdapterManager().getAdapter(this, adapter);
   }

   @Override
   public boolean exists() {
      return true;
   }

   @Override
   public IJavaElement getAncestor(int ancestorType) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public String getAttachedJavadoc(IProgressMonitor monitor) throws JavaModelException {
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
      return elementName;
   }

   @Override
   public int getElementType() {
      // TODO Auto-generated method stub
      return 0;
   }

   @Override
   public String getHandleIdentifier() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IJavaModel getJavaModel() {
      return javaProject.getJavaModel();
   }

   @Override
   public IJavaProject getJavaProject() {
      return javaProject;
   }

   @Override
   public IOpenable getOpenable() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IJavaElement getParent() {
      // TODO Auto-generated method stub
      return null;
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
