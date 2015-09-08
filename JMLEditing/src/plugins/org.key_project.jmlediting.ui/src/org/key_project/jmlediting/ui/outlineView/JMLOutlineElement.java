package org.key_project.jmlediting.ui.outlineView;

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
import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * JML Outline Element can be used as a child to return and get shown in the Outline
 * 
 * @author Timm Lippert
 *
 */

public class JMLOutlineElement implements IJavaElement, ISourceReference {
   private IJavaElement parent;
   private final int type = 100;
   private IASTNode jmlNode;
   
   public JMLOutlineElement(IJavaElement parent, IASTNode node) {
      this.parent = parent;
      this.jmlNode = node;
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
      return parent.getAncestor(ancestorType);
   }

   @Override
   public String getAttachedJavadoc(IProgressMonitor monitor) throws JavaModelException {
      return parent.getAttachedJavadoc(monitor);
   }

   @Override
   public IResource getCorrespondingResource() throws JavaModelException {
      return parent.getCorrespondingResource();
   }

   @Override
   public String getElementName() {
      return jmlNode.toString();
   }

   @Override
   public int getElementType() {
      return type;
   }

   @Override
   public String getHandleIdentifier() {
      // TODO Auto-generated method stub
      return parent.getHandleIdentifier();
   }

   @Override
   public IJavaModel getJavaModel() {
      return parent.getJavaModel();
   }

   @Override
   public IJavaProject getJavaProject() {
      return parent.getJavaProject();
   }

   @Override
   public IOpenable getOpenable() {
      return parent.getOpenable();
   }

   @Override
   public IJavaElement getParent() {
      return parent.getParent();
   }

   @Override
   public IPath getPath() {
      return parent.getPath();
   }

   @Override
   public IJavaElement getPrimaryElement() {
      return parent.getPrimaryElement();
   }

   @Override
   public IResource getResource() {
      return parent.getResource();
   }

   @Override
   public ISchedulingRule getSchedulingRule() {
      return parent.getSchedulingRule();
   }

   @Override
   public IResource getUnderlyingResource() throws JavaModelException {
      return parent.getUnderlyingResource();
   }

   @Override
   public boolean isReadOnly() {
      return false;
   }

   @Override
   public boolean isStructureKnown() throws JavaModelException {
      return parent.isStructureKnown();
   }

   @Override
   public String getSource() throws JavaModelException {
      return "";
   }

   @Override
   public ISourceRange getSourceRange() throws JavaModelException {
      return new ISourceRange() {
         
         @Override
         public int getOffset() {
            return 1;
         }
         
         @Override
         public int getLength() {
            return 1;
         }
      };
   }

   @Override
   public ISourceRange getNameRange() throws JavaModelException {
      return new ISourceRange() {
         
         @Override
         public int getOffset() {
            return  jmlNode.getStartOffset();
         }
         
         @Override
         public int getLength() {
            return jmlNode.getEndOffset()-jmlNode.getStartOffset();
         }
      };
   }

}
