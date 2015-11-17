package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/**
 * Abstract class defining with common behavior of refactoring computers participating in the
 * move or rename refactoring.
 * <p>
 * Changes to the JML annotations of a given java source file can be computed by calling the
 * {@link #computeNeededChangesToJML(ICompilationUnit, IJavaProject)} method, which uses a
 * {@link CommentLocator} to find all JML comments, filters those using the abstract
 * {@link #filterStringNodes(List)} and creates a list of {@link ReplaceEdit}s by calling the
 * abstract method {@link #computeReplaceEdit(ICompilationUnit, ArrayList, HashMap)}.
 * </p>
 * <p>
 * By implementing both abstract methods, one can define the exact behavior of the refactoring
 * computer. For example, one can define if a resolver is called or not.
 * </p>
 * 
 * @author Robert Heimbach
 *
 */
public abstract class AbstractRefactoringComputer implements IRefactoringComputer {

   /**
    * Computes the text changes which need to be done to JML code by finding all JML comments
    * in the file, filtering those and computing the changes.
    * 
    * @param unit {@link ICompilationUnit} for which to create the changes.
    * @param project Project of the compilation unit.
    * @return List of edits which need to be done
    * @throws JavaModelException Thrown when the source file cannot be loaded from
    *            {@link ICompilationUnit} or he JMLcomments could not be received.
    */
   public final ArrayList<ReplaceEdit> computeNeededChangesToJML(ICompilationUnit unit, IJavaProject project) throws JavaModelException {

      final ArrayList<ReplaceEdit> changesToMake = new ArrayList<ReplaceEdit>();

      // Look through the JML comments and find the potential references which
      // might need to be renamed
      final String source = unit.getSource();

      // Get all JML comments
      for (final CommentRange range : CommentLocator.listJMLCommentRanges(source)) {

         // Filter the comments
         final HashMap<IASTNode, List<IStringNode>> foundReferences = getReferencesInJMLcomments(
                  project, source, range);

         // this method is abstract to allow different ways to compute the
         // edits.
         computeReplaceEdit(unit, changesToMake, foundReferences);
      }
      return changesToMake;
   }

   /**
    * Creates the text change for a given JML comment and adds the change to
    * {@code changesToMake}.
    * 
    * @param changesToMake list to add the {@link ReplaceEdit}s to.
    * @param primaryStringMap {@link IASTNode} to compute the change for and the
    *           {@link IStringNode}s which they contain.
    */
   abstract protected void computeReplaceEdit(ICompilationUnit unit,
            ArrayList<ReplaceEdit> changesToMake,
            HashMap<IASTNode, List<IStringNode>> primaryStringMap);

   /**
    * Searches through a given {@link CommentRange} in a source file and returns all JML
    * comments as a list which is potentially empty.
    * 
    * @param project {@link IJavaProject} the source file resides in. Needed to get the
    *           project specific active JMLProfile on which a {@link IJMLParser} is created.
    * @param source String representation of the source file to be used in the
    *           {@link IJMLParser}.
    * @param range CommentRange to be parsed. Specifies the location in the source file to be
    *           checked for JML comments.
    * @return Hash map of found JML comments, represented as {@link IASTNode}s paired with all
    *         the locations of potential references to the element to be refactored stored in
    *         a list of {@link IStringNode}s. The hash map is potentially empty if a
    *         ParserException was thrown or no JML comment was found. Guaranteed to be not
    *         null.
    */
   private final HashMap<IASTNode, List<IStringNode>> getReferencesInJMLcomments(
            IJavaProject project, String source, CommentRange range) {

      List<IASTNode> stringNodes;

      // Get the project specific active JML profile and create a JML parser for
      // it.
      final IJMLProfile activeProfile = JMLPreferencesHelper
               .getProjectActiveJMLProfile(project.getProject());
      final IJMLParser parser = activeProfile.createParser();
      IASTNode parseResult;
      try {
         // Get the JML comments in the given range as string nodes.
         parseResult = parser.parse(source, range);
         stringNodes = Nodes.getAllNodesOfType(parseResult, NodeTypes.STRING);
      }
      catch (final ParserException e) {
         return new HashMap<IASTNode, List<IStringNode>>();
      }

      // Filter the nodes by finding all strings which match the old name of the
      // element to be renamed.
      final List<IStringNode> filteredStringNodes = filterStringNodes(stringNodes);

      // For those occurrences left, find the primary nodes which provide the
      // needed context for resolving.
      final HashMap<IASTNode, List<IStringNode>> primaryStringMap = getPrimaryNodes(
               filteredStringNodes, parseResult);

      return primaryStringMap;
   }

   /**
    * Returns the primary nodes for a given list of string nodes using the context information
    * of the parse result. That is, we look if the given node is part of a larger JML
    * expression.
    * 
    * @param stringNodes list of {@link IStringNode}s for which the corresponding primary
    *           nodes should be returned.
    * @param parseResult An {@link IASTNode} containing the parse result, i.e. the JML
    *           comments in the compilation unit.
    * @return list of {@link IASTNode}s of primary node type.
    */
   private HashMap<IASTNode, List<IStringNode>> getPrimaryNodes(
            final List<IStringNode> stringNodes, final IASTNode parseResult) {
      final HashMap<IASTNode, List<IStringNode>> primaryStringMap = new HashMap<IASTNode, List<IStringNode>>();

      for (final IStringNode stringNode : stringNodes) {

         IASTNode primary = getPrimaryNode(parseResult, stringNode);

         // Some string nodes are not contained in a primary node, e.g. if it is
         // a cast expression and the class destination is renamed
         // or assignable statement in the JML profile (non-KeY profile).
         if (primary == null) {
            primary = stringNode;
         }
         // nested expressions would add the same primary twice, e.g. if code
         // looks like this:
         // TestClass test;
         // /*@ ensures this.test.test ... @*/
         if (!primaryStringMap.containsKey(primary)) {

            // put in a new primary - list of string nodes pair.
            LinkedList<IStringNode> stringNodesForPrimary = new LinkedList<IStringNode>();
            stringNodesForPrimary.add(stringNode);
            primaryStringMap.put(primary, stringNodesForPrimary);
         }
         else {
            // shared primary. more than one string node has the same primary.
            primaryStringMap.get(primary).add(stringNode);
         }
      }
      return primaryStringMap;
   }

   /**
    * This method traverses the JML comment, saved as a {@link IASTNode} to find the primary
    * node of a given {@link IStringNode}.
    * 
    * @param context JML comment which provides the necessary context.
    * @param toTest string node to find the primary node for.
    * @return the primary node of the given string node.
    */
   private IASTNode getPrimaryNode(final IASTNode context, final IStringNode toTest) {
      return context.traverse(new INodeTraverser<IASTNode>() {

         @Override
         public IASTNode traverse(final IASTNode node, IASTNode existing) {
            if (node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
               if (node.containsOffset(toTest.getStartOffset())) {
                  if (existing == null) {
                     existing = node;
                  }
               }
            }
            return existing;
         }
      }, null);
   }

   /**
    * Filters a list of {@link IASTNode} for those which potentially reference the element to
    * be renamed, e.g. by comparing the name.
    * 
    * @param nodesList list to filter. Should be a list of {@link IStringNode}s.
    * @return filtered list the filtered list of nodes.
    */
   protected abstract List<IStringNode> filterStringNodes(final List<IASTNode> nodesList);
}
