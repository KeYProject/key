package org.key_project.jmlediting.ui.outline;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.key_project.javaeditor.util.LogUtil;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.jmlediting.core.dom.NodePrinter;

/**
 * Locates JML Comments for the given JDT AST.
 * 
 * @author Timm Lippert
 *
 */
public class JMLASTCommentLocator {

   /**
    * Lists to return for outline with necessary comments and underlying AST nodes.
    */
   private ArrayList<JMLComments> jmlForMethodList = new ArrayList<JMLComments>();
   private ArrayList<JMLComments> jmlClassList = new ArrayList<JMLComments>();
   private final Map<Integer, Integer> sourceOffsetToCommentOffset;
   private final Map<Integer, JMLComments> fieldDeclarationMap;
   private final Map<Integer, JMLComments> methoddDeclarationMap;

   private final List<int[]> methodStartEndoffsets = new ArrayList<int[]>();
   private final List<int[]> fieldStartToEnd = new ArrayList<int[]>();

   private List<Comment> comments;
   private String[] methodKeyWords = { "normal_behavior", "normal_behaviour", "behavior",
            "behaviour", "exceptional_behaviour", "exceptional_behavior" };

   /**
    * Constructor for {@link JMLASTCommentLocator}. It gets all {@link Comment} of the
    * {@link ICompilationUnit} and saves all JML Comments.
    * 
    * @param icu {@link ICompilationUnit} Unit of the Project
    * 
    */

   @SuppressWarnings("unchecked")
   public JMLASTCommentLocator(ICompilationUnit icu) {
      String source = null;
      IASTNode node = null;
      List<IASTNode> listofIAST;
      // Source is needed to get comments out of text with getCommentlist
      try {
         source = icu.getSource();
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }
      // get all resources needed
      final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(icu);
      CompilationUnit cu = (CompilationUnit) jdtAST;
      comments = cu.getCommentList();

      // we only have start information of comments but not the content.
      sourceOffsetToCommentOffset = new HashMap<Integer, Integer>();
      fieldDeclarationMap = new HashMap<Integer, JMLComments>();
      methoddDeclarationMap = new HashMap<Integer, JMLComments>();
      // iterate over Field and method declarations to get all start and length information
      jdtAST.accept(new ASTVisitor() {

         @Override
         public boolean visit(FieldDeclaration node) {
            int[] a = { node.getStartPosition(), node.getLength() };
            fieldStartToEnd.add(a);

            return super.visit(node);
         }

         @Override
         public boolean visit(MethodDeclaration node) {
            // get needed offsets.
            try {
               int offset = 0;
               if (node.resolveBinding() != null) {
                  offset = ((IMethod) node.resolveBinding().getJavaElement()).getNameRange()
                           .getOffset();
                  sourceOffsetToCommentOffset.put(((IMethod) node.resolveBinding()
                           .getJavaElement()).getNameRange().getOffset(), jdtAST
                           .firstLeadingCommentIndex(node));
               }
               int[] nodeStartLength = { node.getStartPosition(), node.getLength(), offset };
               methodStartEndoffsets.add(nodeStartLength);

            }
            catch (JavaModelException e) {
               LogUtil.getLogger().logError(e);
            }

            return super.visit(node);

         }
      });

      IJMLProfile p = JMLPreferencesHelper.getProjectActiveJMLProfile(icu.getJavaProject()
               .getProject());

      IJMLParser parser = p.createParser();
      // Get keywords for JML to check for
      // iterate over comments and make different lists for comments
      String text, keyword = null;

      if (source != null) {
         for (Comment currentComment : comments) {
            if (!currentComment.isDocComment()) {
               text = source.substring(currentComment.getStartPosition(),
                        currentComment.getLength() + currentComment.getStartPosition());
               if (isJMLComm(text)) {
                  // if JML comm then make readable Text and get Keyword of
                  text = removeJMLComm(text, ((Comment) currentComment).isBlockComment());
                  try {
                     node = parser.parse(text, 0, text.length());

                     listofIAST = node.getChildren();
                     keyword = getFirstKeyword(listofIAST.get(0));
                     if (keyword == null)
                        keyword = getFirstKeyword(listofIAST.get(1));

                     text = NodePrinter.print(node).trim();

                     // check to what the comment belongs to and add to respective list.
                     if (formethod(keyword)) {
                        jmlForMethodList.add(new JMLComments(text, currentComment));
                     }
                     else if (commentInMethod(currentComment.getStartPosition(),
                              currentComment, text)) {
                     }
                     else if (commentInField(currentComment.getStartPosition(),
                              currentComment, text)) {
                     }
                     else if (notInMethod(currentComment.getStartPosition())) {
                        jmlClassList.add(new JMLComments(text, currentComment));
                     }
                  }
                  catch (ParserException e) {
                  }

               }
            }
         }
      }
   }

   private boolean commentInMethod(int startPosition, Comment com, String text) {
      for (int[] i : methodStartEndoffsets) {
         if (startPosition >= i[0] && startPosition <= (i[2])) {
            methoddDeclarationMap.put(i[2], new JMLComments(text, com));
            return true;
         }
      }
      return false;
   }

   private boolean commentInField(int startPosition, Comment com, String text) {
      for (int[] i : fieldStartToEnd) {
         if (startPosition >= i[0] && startPosition <= (i[1] + i[0])) {
            fieldDeclarationMap.put(i[0] + i[1], new JMLComments(text, com));
            return true;
         }
      }
      return false;
   }

   private boolean notInMethod(int start) {
      boolean ret = false;
      for (int[] a : methodStartEndoffsets) {
         if (((start > a[0]) && (start < (a[1] + a[0])))) {
            return false;
         }
         else {
            ret = true;
         }
      }
      return ret;
   }

   private String getFirstKeyword(IASTNode iastNode) {
      if (iastNode.getType() == NodeTypes.KEYWORD) {
         if (isRealKeyword(((IKeywordNode) iastNode).getKeywordInstance())) {
            return ((IKeywordNode) iastNode).getKeywordInstance();
         }
      }
      else if (iastNode.getType() == NodeTypes.KEYWORD_APPL) {
         return getFirstKeyword(iastNode.getChildren().get(0));
      }
      return null;
   }

   private boolean isRealKeyword(String keywordInstance) {
      if (keywordInstance.equals("public") || keywordInstance.equals("protected")
               || keywordInstance.equals("private")) {
         return false;
      }
      return true;
   }

   private boolean isJMLComm(String text) {
      // only take JML Comments declared with /*@
      return (text.contains("/*@") || text.contains("//@"));
   }

   private boolean formethod(String keyword) {
      for (String s : methodKeyWords) {
         if (keyword.equals(s))
            return true;
      }
      return false;
   }

   /**
    * make pretty string.
    */
   private String removeJMLComm(String text, boolean isblock) {
      // remove useless space for outline
      if (isblock) {
         // replace JML specific Comment stuff to make it pretty and easier to
         // read
         text = text.substring(3, text.length() - 3);
      }
      else
         text = text.replaceFirst("//@", "");
      if (text.startsWith(" ")) {
         text = text.replaceFirst("\\s+", "");
      }
      return text;
   }

   /**
    * Gets all JML Comments which are underneath the Class and not in a function or a Field
    * declaration.
    * 
    * @return List of JML Comments with Text.
    */
   public final List<JMLComments> getClassInvariants() {

      return jmlClassList;
   }

   /**
    * Gets the matching comment for the method.
    * 
    * @param offset offset of {@link IMethod} which the comment should be found for
    * @return All Comments for the given Method offset if it has a JML comment as first
    *         leading comment else null.
    */
   public final List<JMLComments> getMethodJMLComm(int offset) {
      List<JMLComments> retlist = new ArrayList<JMLComments>();
      int commlocationinList = -1;
      // look if method is in hashmap
      if (sourceOffsetToCommentOffset.containsKey(offset)) {
         commlocationinList = sourceOffsetToCommentOffset.get(offset);
         if (commlocationinList != -1) {
            for (JMLComments comment : jmlForMethodList) {
               if (comment.getStartOffset() <= offset
                        && comment.getStartOffset() >= comments.get(commlocationinList)
                                 .getStartPosition()) {
                  retlist.add(comment);
                  break;
               }
            }
         }
         if (methoddDeclarationMap.containsKey(offset)) {
            retlist.add(methoddDeclarationMap.get(offset));
         }
      }
      return retlist;
   }

   /**
    * Gets the matching Comments for a given @ {@link IFile}'s {@link ISourceRange}'s offset +
    * length.
    * 
    * @param offset Should be {@link IFile}'s {@link ISourceRange} offset + length.
    * @return The {@link JMLComments} for the given offset.
    */
   public final JMLComments getFieldJMLComm(int offset) {
      return fieldDeclarationMap.get(offset);
   }
}