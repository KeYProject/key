package org.key_project.jmlediting.ui.outlineView;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.internal.codeassist.impl.Keywords;
import org.eclipse.jdt.internal.core.search.matching.MethodLocator;
import org.eclipse.jdt.internal.ui.preferences.formatter.CommentsTabPage;
import org.key_project.javaeditor.util.LogUtil;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.ui.wizard.JMLKeywordWizard;
import org.key_project.util.jdt.JDTUtil;

/**
 * Locates JML Comments with JDT AST
 * 
 * @author Timm Lippert
 *
 */

public class JMLASTCommentLocator {
   
   /**
    * Lists to return for outline with necessary comments and underlying AST nodes
    */
   ArrayList<JMLComents> methodesList = new ArrayList<JMLComents>();
   ArrayList<JMLComents> invariantList = new ArrayList<JMLComents>();
   ArrayList<JMLComents> loopInvariantList = new ArrayList<JMLComents>();
   final Map<Integer, Integer> sourceOffsetToCommentOffset;
   
   
   
   
   List<?> comments;
   
   Set<IKeyword> keywords = null;
   String [] methodKeyWords  = {"normal_behavior","exeptional_behavior"};
   String [] invariantKeyWords  = {"invariant"};
   String [] loopinvarinatKeyWords  = {"loop_invariant","maintaining"};
   
   /**Constructor for /{@link JMLASTCommentLocator} </br> gets all {@link Comment} of the {@link ICompilationUnit} and saves all JML Comments
    * 
    * @param icu {@link ICompilationUnit} Unit of the Project
    * 
    */
   
   
   public JMLASTCommentLocator(ICompilationUnit icu) {
      CompilationUnit cu;
      String source = null;
      IASTNode node = null;
      //Source is needed to get comments out of text with getCommentlist
      try {
         source = icu.getSource();
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }
      //get all resources needed
      final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(icu);
      cu = (CompilationUnit) jdtAST; // TODO .. ?! :O
      comments = cu.getCommentList();
      //return indext in list
      sourceOffsetToCommentOffset = new HashMap<Integer, Integer>();
      jdtAST.accept(new ASTVisitor() {
         
         @Override
         public boolean visit(MethodDeclaration node) {
            // Cast missing to IMethod node.resolveBinding().getJavaElement();
            try {
               sourceOffsetToCommentOffset.put(((IMethod)node.resolveBinding().getJavaElement()).getNameRange().getOffset() , jdtAST.firstLeadingCommentIndex(node));
            }
            catch (JavaModelException e) {
               LogUtil.getLogger().logError(e);
            }
            
            return super.visit(node);
            
         }
      });
      
      //######################################################
      //TODO: Wichtig !! kommentare versuchen über JML Parser auszulesen um Keywords zu bekommen
      
      
      IJMLProfile p = JMLPreferencesHelper.getProjectActiveJMLProfile(icu.getJavaProject().getProject());
      IJMLParser parser = p.createParser();
      //Get keywords for JML to check for
      if (p != null) keywords = p.getSupportedKeywords();
      else keywords = JMLPreferencesHelper.getDefaultDefaultJMLProfile().getSupportedKeywords();
      
      
      for (IKeyword k : keywords){
         System.out.println(k.toString());
         
         for(String s : k.getKeywords()) {
            System.out.println('\t'+s);
         }
      }
      
      
      //iterate over comments and make different lists for comments
      String text, keyword;
      IKeyword [] keyarray ={};
      Comment currentcomment;
      if (keywords != null)
         keyarray = keywords.toArray(keyarray);
      
      if(source != null){
         for (Object obj : comments) {
            if (obj instanceof Comment) {
               currentcomment = (Comment)obj; 
               if (!currentcomment.isDocComment()){
                  text = source.substring(currentcomment.getStartPosition(), currentcomment.getLength()+currentcomment.getStartPosition());
                  /*try {
                     node = parser.parse(text, 0, text.length());
                  }
                  catch (ParserException e) {
                     LogUtil.getLogger().logError(e);
                  }*/
                     if (isJMLComm(text)){
                        //if JML comm then make readable Text and get Keyword of it
                        text = removeKomm(text, ((Comment)obj).isBlockComment());
                        keyword = getKeyWord(text);
                        //TODO: Check all key words(all dialects) figure out how to get them from highlighting
                           if(keyword.equals(methodKeyWords[0])){
                              methodesList.add( new JMLComents(text, currentcomment,"method"));
                           }else
                           if(keyword.equals(invariantKeyWords[0])){
                              invariantList.add(new JMLComents(text, currentcomment, "invariant"));                           
                           }else
                           if(keyword.equals(loopinvarinatKeyWords[0])) {
                              loopInvariantList.add(new JMLComents(text, currentcomment, "loop_invariant"));
                           }else System.out.println(text);
                     }
                     
               }
            }
         }
      }
   }
   
   /**
    * 
    * @param text the text that should get checkt if it is a jml comment
    * @return true if it is a comment by knowing it contains "/*@" or "//@" for initializing a JML comment
    */
   private boolean isJMLComm(String text) {
      //only take JML Comments declared with /*@
      return (text.contains("/*@") || text.contains("//@") );
   }
   
   /**Returns the first word as Keyword
    * 
    */
   private String getKeyWord(String text) {
      //first element should be keyword in JML
      return text.split(" ")[0];
   }
   
   
   /**
    * make pretty string
    */
   private String removeKomm(String text, boolean isblock) {
      //remove useless space for outline
      if (isblock) {
         //replace JML specific Comment stuff to make it pretty and easier to read
      text = text.replaceAll("@", "");
      text = text.replaceAll("\\*/","");
      text = text.replaceAll("/\\*", "");
      } else text =  text.replace("//@", "");
      text = text.replaceAll("\\s\\s+", " ");
      text = text.replaceAll("\\n+", "");
      text = text.replaceAll("\\t+", "");
      if(text.startsWith(" ")) {
         text = text.replaceFirst("\\s+", "");
      }
      return text; 
   }
   
   /**
    *  Gets all JML Comments wich are Invariants in {@link JMLComents} Object
    * @return List of JML Comments with Text
    */
   public List<JMLComents> getClassInvariants() {
      
      return invariantList;
   }
   
   /**
    *  Gets all JML Comments wich are Loop Invariants in a {@link JMLComents} Object
    * @return List of JML Comments with Text
    */
   public List<JMLComents> getLoopInvariants() {
      
      return loopInvariantList;
   }


   /**
    * Gets the matching comment for the method
    * @param offset offset of IMethod wich the comment should be found for
    * @return Comment if it has a JML comment as first leading comment else null
    */
   public JMLComents getmethodJMLComm (int offset) {
      int commlocationinList;
    //look if method is in hashmap
      if(sourceOffsetToCommentOffset.containsKey(offset)){
         commlocationinList = sourceOffsetToCommentOffset.get(offset);
         if(commlocationinList != -1){
            for(JMLComents com : methodesList) {
               if (com.getStartOffset() == ((Comment)comments.get(commlocationinList)).getStartPosition()) {
                  return com;
               }
            }
         }
      }
      return null;
   }
   /**
    * Returns fo a given method offset and his length the loop invariant if available
    * @param offset offset of {@link IMethod}
    * @param length length of {@link IMethod}
    * @return JMLComents for the given IMethod or null of not available
    */
   public List<JMLComents> getLoopInvaForMethod(int offset,int length) {
      List<JMLComents> invsinmethod = new ArrayList<JMLComents>();
      for (JMLComents com : loopInvariantList) {
         System.out.println("Kommentar start ::"+com.getStartOffset()+"\t end:: "+com.getEndOffset() );
         System.out.println("Function offset::"+offset+ "\t end:: " + length+offset);
         if(com.getStartOffset() > offset && com.getEndOffset() < length) {
            invsinmethod.add(com);
         }
      }return invsinmethod;
   }
   
}
