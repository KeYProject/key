package org.key_project.jmlediting.ui.outline;

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
 * JML Outline Element can be used as a child to return and get shown in the Outline.
 * 
 * @author Timm Lippert
 *
 */
public class JMLOutlineElement implements IJavaElement, ISourceReference {
   private IJavaElement parent;
   private static final int type = 100;
   private IASTNode jmlNode;
   
   /**
    * Constructor. Saves the parent and the node to show.
    * 
    * @param parent element to which the node should be added.
    * @param node node to show.
    */
   public JMLOutlineElement(IJavaElement parent, IASTNode node) {
      this.parent = parent;
      this.jmlNode = node;
   }

   @SuppressWarnings("rawtypes")
   @Override
    public final Object getAdapter(Class adapter) {
      return Platform.getAdapterManager().getAdapter(this, adapter);
   }

   @Override
   public final boolean exists() {
      return true;
   }

   @Override
   public final IJavaElement getAncestor(int ancestorType) {
      return parent.getAncestor(ancestorType);
   }

   @Override
   public final String getAttachedJavadoc(IProgressMonitor monitor) throws JavaModelException {
      return parent.getAttachedJavadoc(monitor);
   }

   @Override
   public final IResource getCorrespondingResource() throws JavaModelException {
      return parent.getCorrespondingResource();
   }

   @Override
   public final String getElementName() {
      return jmlNode.toString();
   }

   @Override
   public final int getElementType() {
      return type;
   }

   @Override
   public final String getHandleIdentifier() {
      return parent.getHandleIdentifier();
   }

   @Override
   public final IJavaModel getJavaModel() {
      return parent.getJavaModel();
   }

   @Override
   public final IJavaProject getJavaProject() {
      return parent.getJavaProject();
   }

   @Override
   public final IOpenable getOpenable() {
      return parent.getOpenable();
   }

   @Override
   public final IJavaElement getParent() {
      return parent.getParent();
   }

   @Override
   public final IPath getPath() {
      return parent.getPath();
   }

   @Override
   public final IJavaElement getPrimaryElement() {
      return parent.getPrimaryElement();
   }

   @Override
   public final IResource getResource() {
      return parent.getResource();
   }

   @Override
   public final ISchedulingRule getSchedulingRule() {
      return parent.getSchedulingRule();
   }

   @Override
   public final IResource getUnderlyingResource() throws JavaModelException {
      return parent.getUnderlyingResource();
   }

   @Override
   public final boolean isReadOnly() {
      return false;
   }

   @Override
   public final boolean isStructureKnown() throws JavaModelException {
      return parent.isStructureKnown();
   }

   @Override
   public final String getSource() throws JavaModelException {
      return "";
   }

   @Override
   public final ISourceRange getSourceRange() throws JavaModelException {
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
   public final ISourceRange getNameRange() throws JavaModelException {
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
