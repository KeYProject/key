package org.key_project.jmlediting.core.dom.internal;

import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolverException;

/**
 * An ASTNode implements a default AST node.
 *
 * @author Moritz Lichter
 *
 */
public class ASTNode extends AbstractASTNode {

   /**
    * The type of the node.
    */
   private final int type;
   /**
    * The list of all children.
    */
   private final List<IASTNode> children;

   /**
    * The profile of the node
    */
   private final IJMLProfile profile;
   
   /**
    * Creates a new {@link ASTNode}. The start offset needs to be less than or
    * equal to the end offset.
    *
    * @param startOffset
    *           the start offset
    * @param endOffset
    *           the end offset
    * @param type
    *           the type of the node
    * @param children
    *           the list of children of the node, may be null
    */
   public ASTNode(final int startOffset, final int endOffset, final int type,
         final List<IASTNode> children, IJMLProfile profile) {
      super(startOffset, endOffset);
      if (NodeTypes.getTypeName(type) == null) {
         throw new IllegalArgumentException(
               "Creates node with unregistered type " + type);
      }
      this.profile=profile;
      this.type = type;
      this.children = children;
      // Validate children
      int begin = startOffset;
      for (final IASTNode child : children) {
         if (child.getStartOffset() < begin) {
            throw new IllegalArgumentException(
                  "Start offset off child is invalid: child begin "
                        + child.getStartOffset() + " is less than " + begin);
         }
         begin = child.getEndOffset();
      }
      if (begin > endOffset) {
         throw new IllegalArgumentException(
               "End offset of last child exceed node");
      }
   }

   @Override
   public int getType() {
      return type;
   }

   @Override
   public List<IASTNode> getChildren() {
      // We need to return a non null list in any case
      if (children == null) {
         return Collections.emptyList();
      }
      else {
         return Collections.unmodifiableList(children);
      }
   }

    @Override
    public IJMLProfile getProfile() {
        // TODO DECLARED PROFILE FOR THE CLASS AND ADDED ENTRY TO CONSTRUCTOR
        return this.profile;
    }
    
    @Override
    public ResolveResult resolve(ICompilationUnit cu) {
        // TODO CALL RESOLVE FROM THE PROFILE, HOW DO I GET COMPILATION UNIT??? GAVE IT AS A PARAMETER, CHECK PLX
        try {
            return getProfile().getResolver().resolve(cu, this);
        }
        catch (ResolverException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return null;
        }
    }

}
