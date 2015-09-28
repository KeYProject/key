package org.key_project.jmlediting.profile.jmlref.resolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.LogUtil;

/**
 * This class is used by the {@link Resolver} at the beginning stage when gathering information.
 * <br><br>
 * The using class will need to call the only available method,
 * {@link #getSearchContext(IASTNode)}, and will return the {@link ASTNode} for a given
 * {@link IASTNode}. That is, the context information to which a JML comment refers to.
 * 
 * @author Christopher Beckmann, Robert Heimbach
 *
 */
public class SearchContextMapper {

   private final CompilationUnit jdtAST;
   private final ICompilationUnit compilationUnit;

   /**
    * The constructor saves the {@link ICompilationUnit} and the {@link CompilationUnit}.
    * 
    * @param compilationUnit a given {@link ICompilationUnit} which we should search through.
    * @param jdtAST the AST of the parsed {@code compilationUnit}
    */
   SearchContextMapper(final ICompilationUnit compilationUnit, final CompilationUnit jdtAST) {
      this.compilationUnit = compilationUnit;
      this.jdtAST = jdtAST;
   }

   /**
    * Returns the ASTNode which belongs to a given {@link IASTNode}. Usually this is a field
    * or method declaration but it can also be a class itself in case of a class invariant.
    * 
    * @param jmlNode the {@link IASTNode} for which the {@link ASTNode} should be found.
    * @return the {@link ASTNode} which belongs to the given {@link IASTNode}. Can be {@code null} if nothing was
    *         found.
    */
   public final ASTNode getSearchContext(final IASTNode jmlNode) {

      final HashMap<Comment, ASTNode> commentToAST = new HashMap<Comment, ASTNode>();

      // Locate all the comments
      String source = null;
      try {
         source = compilationUnit.getSource();
      }
      catch (final JavaModelException e) {
         // CompilationUnit has no source attached to it?
         LogUtil.getLogger().logError(e);
         return null;
      }

      // Finding the full JML comment which contains our IASTNode we need to resolve by
      // getting all JDT comments (everything with // or /*)
      // and filtering those for comments which start with either //@ or /*@
      @SuppressWarnings("unchecked")
      final List<Comment> jdtComments = jdtAST.getCommentList();

      final ArrayList<Comment> jmlComments = new ArrayList<Comment>();

      Comment jmlComment = null;

      // Filtering the JDT comments
      for (final Comment comment : jdtComments) {

         final int commentStart = comment.getStartPosition();
         final String stringToCompare = source.substring(commentStart, commentStart + 3);

         if (stringToCompare.equals("//@") || stringToCompare.equals("/*@")) {
            jmlComments.add(comment);

            // check if the JML comment contains our IASTNode that is
            // supposed to be resolved
            if (commentStart <= jmlNode.getStartOffset()
                  && commentStart + comment.getLength() >= jmlNode.getEndOffset()) {
               jmlComment = comment;
            }
         }
      }

      // this maps every JML comment to the JDT ASTNode it belongs to.
      jdtAST.accept(new ASTVisitor() {

         @Override
         public boolean preVisit2(final ASTNode node) {
            // Check if the node has a comment at all
            final int start = jdtAST.firstLeadingCommentIndex(node);
            if (start != -1) {
               // extended start = start if JML in between Javadoc and Node (e.g. method)
               // extended start < start if JML above Javadoc.
               // Note that it will not be extended if an empty line is between JML and
               // Javadoc.
               final int extStartNode = jdtAST.getExtendedStartPosition(node);
               final int extEndNode = extStartNode + jdtAST.getExtendedLength(node);
               // JML belongs to the node if it is in between the extended
               // area covered by the node
               for (final Comment comment : jmlComments) {
                  final int commentStart = comment.getStartPosition();
                  final int commentEnd = commentStart + comment.getLength();
                  if (commentStart >= extStartNode && commentEnd < extEndNode) {
                     if (node.getNodeType() == ASTNode.PRIMITIVE_TYPE
                           || node.getNodeType() == ASTNode.SIMPLE_TYPE) {
                        commentToAST.put(comment, node.getParent());
                     }
                     else {
                        commentToAST.put(comment, node);
                     }
                  }
               }
            }
            return super.preVisit2(node);
         }
      });

      // Check if there are any JML comments not yet mapped.
      // Those should be class invariants not directly written above a field or such.
      // Put the TypeDecleration of the CompilationUnit/ASTNode into commentToAST.
      // Method invariants should have been mapped before.
      for (final Comment comment : jmlComments) {
         if (!commentToAST.containsKey(comment)) {
            final ASTNode compUnitType = Resolver.getTypeInCompilationUnit(
                  compilationUnit.getElementName().substring(0,
                        compilationUnit.getElementName().lastIndexOf('.')), jdtAST);
            commentToAST.put(comment, compUnitType);
         }
      }

      return commentToAST.get(jmlComment);
   }
}
