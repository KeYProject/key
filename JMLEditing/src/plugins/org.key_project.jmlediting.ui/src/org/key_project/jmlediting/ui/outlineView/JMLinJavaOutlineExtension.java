package org.key_project.jmlediting.ui.outlineView;



import java.util.List;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.javaeditor.outline.DefaultOutlineModifiyer;
import org.key_project.javaeditor.util.LogUtil;

/**
 * Extends the Java Outline with JML Specifications.
 * 
 * @author Timm Lippert
 *
 */
public class JMLinJavaOutlineExtension extends DefaultOutlineModifiyer {

   
   private JMLASTCommentLocator comments = null;
   private IJavaElement root = null;
   
   @Override
   public Object[] modify(Object parent, Object[] currentChildren) {
      
      if(!(parent instanceof IJavaElement)){
         return currentChildren;
      }
      
      final IJavaElement javaParent = (IJavaElement)parent;
      
      //first call with i compilation unit initialize everything
      if(javaParent.getParent().getElementType() == IJavaElement.PACKAGE_FRAGMENT) {
         comments = new JMLASTCommentLocator((ICompilationUnit)javaParent);
         root =  javaParent;
      }else if (comments == null) return currentChildren;
      
      if (comments != null) {
   
         // add invariants to class
         if (javaParent.getElementType() == IJavaElement.TYPE && javaParent.getParent().equals(root)){
         
            Object[] newArray = new Object[currentChildren.length+comments.getClassInvariants().size()];
            
           //add old elements
            for (int i =  comments.getClassInvariants().size(); i < currentChildren.length+comments.getClassInvariants().size(); i++){
               newArray[i] = currentChildren[i-comments.getClassInvariants().size()];
            }
            int i = 0;
            //add JML elements
            for(JMLComments node : comments.getClassInvariants()) {
               newArray[i++] = new JMLOutlineElement((IJavaElement)parent, node);
            }
            return newArray;
         }
         
         // add JML #Spezifications to methods   
         if (javaParent.getElementType() == IJavaElement.METHOD){
            IMethod method = (IMethod)javaParent;
            int offset = -1;
            int arroffset = 0;
            List<JMLComments> comlist = null;
            Object[] newArray;
            
            try {
               offset = method.getNameRange().getOffset();
            }catch (JavaModelException e) {
               LogUtil.getLogger().logError(e);;
            }
            
            
            comlist  = comments.getMethodJMLComm(offset);
            
            if (comlist != null)  {
               
               arroffset = comlist.size();
               newArray = new Object[currentChildren.length+arroffset];
               int i=0;
               for (JMLComments com : comlist){
                  newArray[i++] = new JMLOutlineElement((IJavaElement) parent, com);
               }
               for (i = offset; i < newArray.length; i++){
                  newArray[i] = currentChildren[i-1];
               }
            } else newArray = currentChildren;
            
            return newArray;
               
            
              
         }
         // add field declarations
         if (javaParent.getElementType() == IJavaElement.FIELD){
            IField field = (IField) javaParent;
            JMLComments toAdd = null;
            Object [] newarray;
            
            
            
            try {
               toAdd = comments.getFieldJMLComm(field.getSourceRange().getLength()+field.getSourceRange().getOffset());
            }
            catch (JavaModelException e) {
               LogUtil.getLogger().logError(e);
            }
            if (toAdd != null) {
               newarray = new Object[currentChildren.length+1];
               newarray[0] = new JMLOutlineElement(javaParent, toAdd);
               for (int i= 1; i <= currentChildren.length; i++){
                  newarray[i] = currentChildren[i-1];
               }
            }else newarray = currentChildren;
            
            return newarray;
            
         }
         
      }
      return currentChildren;
  }
}
