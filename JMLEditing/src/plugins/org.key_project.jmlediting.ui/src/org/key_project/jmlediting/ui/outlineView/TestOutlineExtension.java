package org.key_project.jmlediting.ui.outlineView;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.xml.soap.Node;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.javaeditor.outline.DefaultOutlineModifiyer;
import org.key_project.javaeditor.util.LogUtil;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.util.jdt.JDTUtil;

public class TestOutlineExtension extends DefaultOutlineModifiyer {

   
   public static HashMap<String, Object> inOutlie = new HashMap<String, Object>();
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
         for(JMLComents node : comments.getClassInvariants()) {
            newArray[i++] = new JMLOutlineElement((IJavaElement)parent, node);
         }
         return newArray;
         }
         
   // add JML #Spezifications to methods   
         if (javaParent.getElementType() == IJavaElement.METHOD){
            IMethod method = (IMethod) javaParent;
            List<JMLComents> invariants = new ArrayList<JMLComents>();
            int offset = -1;
            int length = -1;
            int arrayoffset = 0;
            
            JMLComents com = null;
            try {
            offset = method.getNameRange().getOffset();
            length = method.getNameRange().getLength();
            }catch (JavaModelException e) {
               LogUtil.getLogger().logError(e);;
            }
            
            com  = comments.getmethodJMLComm(offset);
            if (com != null) invariants.add(com);
            invariants.addAll(comments.getLoopInvaForMethod(offset, length));
            
            //add all loop invs and methods Spezifications
            Object[] newArray = new Object[currentChildren.length+invariants.size()];
            
            
            
            for (int i =0; i < invariants.size(); i++){
               newArray[i] = new JMLOutlineElement((IJavaElement) parent, invariants.get(i));   
            }
            for (int i = invariants.size(); i < newArray.length; i++){
               newArray[i] = currentChildren[i-invariants.size()];
            }
            return newArray;
               
            
              
         }
         
      }
      return currentChildren;
  }
}
