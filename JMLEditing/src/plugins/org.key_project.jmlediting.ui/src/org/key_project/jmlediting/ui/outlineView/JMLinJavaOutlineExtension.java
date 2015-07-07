package org.key_project.jmlediting.ui.outlineView;



import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.javaeditor.outline.DefaultOutlineModifiyer;
import org.key_project.javaeditor.util.LogUtil;

public class JMLinJavaOutlineExtension extends DefaultOutlineModifiyer {

   
   public static JMLASTCommentLocator comments = null;
   
   
   @Override
   public Object[] modify(Object parent, Object[] currentChildren) {
      
      
      final IJavaElement javaParent = (IJavaElement)parent;
      
//first call with i compilation unit initialize everything
      if(javaParent.getElementType() == IJavaElement.COMPILATION_UNIT) {
         comments = new JMLASTCommentLocator((ICompilationUnit)javaParent);  
      }
      
      if (comments != null) {
   // add invariants to class
         if (javaParent.getElementType() == IJavaElement.TYPE){
         
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
            JMLComments com = null;
            Object[] newArray;
            
            try {
            offset = method.getNameRange().getOffset();
            }catch (JavaModelException e) {
               LogUtil.getLogger().logError(e);;
            }
            
            com  = comments.getMethodJMLComm(offset);
            
            if (com != null)  {
               
               arroffset = 1;
               newArray = new Object[currentChildren.length+arroffset];
               newArray[0] = new JMLOutlineElement((IJavaElement) parent, com);
               for (int i = offset; i < newArray.length; i++){
                  newArray[i] = currentChildren[i-1];
               }
            } else newArray = currentChildren;
            
            return newArray;
               
            
              
         }
         
      }
      return currentChildren;
  }
}
