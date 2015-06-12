package org.key_project.jmlediting.ui.outlineView;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
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


public static int count = 0;

   
   public static HashMap<String, Object> inOutlie = new HashMap<String, Object>();
  
   @Override
   public Object[] modify(Object parent, Object[] currentChildren) {

      System.out.println(count++);
      
      
      final IJavaElement javaParent = (IJavaElement)parent;
      final List<IASTNode> iASTList = new ArrayList<IASTNode>();
      
      
      
      if(javaParent.getElementType() == IJavaElement.COMPILATION_UNIT) {
         String source = null;
         try {
            source = ((ICompilationUnit)javaParent).getSource();
         }
         catch (JavaModelException e1) {
            LogUtil.getLogger().logError(e1);
         }
         IProject project = javaParent.getJavaProject().getProject();
         
         final IJMLParser parser;
         
         if (JMLPreferencesHelper.getProjectJMLProfile(project) != null) {
                  
          parser = JMLPreferencesHelper.getProjectJMLProfile(project).createParser();
         }
         else parser = JMLPreferencesHelper.getDefaultDefaultJMLProfile().createParser();
        
         /*
         ICompilationUnit compilationUnit = (ICompilationUnit)javaParent;
         ASTNode node = JDTUtil.parse(compilationUnit);
         CompilationUnit cu = (CompilationUnit) node;
         List comments = cu.getCommentList();
         for (Object obj : comments) {
            if (obj instanceof Comment) {
               Comment bc = (Comment) obj;
               System.out.println(bc.getStartPosition());
               System.out.println(bc.getLength());
               System.out.println(bc.getAlternateRoot());
            }
            System.out.println(obj);
         }
         */
         CommentLocator locator = new CommentLocator(source);
         for(final CommentRange range : locator.findCommentRanges()) {
            try {
               iASTList.add(parser.parse(source, range));
            }
            catch (ParserException e) {
               LogUtil.getLogger().logError(e);
            }
         }
      }
      
      
      
      
      
      Object[] newArray = new Object[currentChildren.length+iASTList.size()];
      
      for (int i =  0; i < currentChildren.length; i++){
         newArray[i] = currentChildren[i];
      }
      
      
      int i = 0;
      final List<String> keywordList = new ArrayList<String>();
      keywordList.add("normal_behavior");
      keywordList.add("invariant");
      final List<IASTNode> keywords = new ArrayList<IASTNode>();
      
      for(IASTNode node : iASTList) {
         node.traverse(new INodeTraverser<List<IASTNode>>() {

            @Override
            public List<IASTNode> traverse(IASTNode node, List<IASTNode> existing) {
               
               if(node.getType() == NodeTypes.KEYWORD) {
                  for(String key : keywordList) {
                     if(((IKeywordNode)node).getKeywordInstance().equals(key)) {
                        keywords.add(node);
                        return keywords;
                     }
                  }
               }               
               return keywords;
            }
         }, keywords);
      }
      
      for(IASTNode node : keywords) {
         newArray[currentChildren.length+i++] = new JMLOutlineElement((IJavaElement)parent, node);
      }
      
      return newArray;
  }
      
      
      
  /*    if (currentChildren.length >= 1 && currentChildren[0] instanceof IJavaElement) {
         Object[] newChildren = new Object[currentChildren.length];
         System.arraycopy(currentChildren, 0, newChildren, 0, currentChildren.length);
         IJavaElement firstChild = (IJavaElement) currentChildren[0];
         System.out.println("Parent: Type:  "+(((IJavaElement)parent).getElementType()));
         System.out.println("Parent: Name:  "+ ((IJavaElement)parent).getElementName());
         
        
         //newChildren[currentChildren.length] = new NoRealJavaElement(firstChild.getJavaProject(), "Hello World");
         //newChildren[currentChildren.length + 1] = new NoRealJavaElement(firstChild.getJavaProject(), "Achtung");
         for (int i = 0; i < newChildren.length; i++) {
            if(newChildren[i] != null) {
               if (newChildren[i] instanceof IJavaElement) {
                  System.out.println(i+" :: ElementType :: "+((IJavaElement)newChildren[i]).getElementType());
                  System.out.println(i+" :: ElementName :: "+((IJavaElement)newChildren[i]).getElementName());
               }
            }
         }
         
         
         return newChildren;
      }
      else {
         return currentChildren;
      }
   }*/
}
