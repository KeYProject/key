package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
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
 * Abstract class with the common behavior of refactoring computers which
 * participant in the move refactoring. 
 * <p>
 * Usually, the move refactoring, does not need to use the resolver. Thus, 
 * in contrast to {@link RenameRefactoringComputer} changes are directly
 * done to the found and filtered JML nodes and easier to compute. </p>
 * <p>
 * See {@link #computeNeededChangesToJML(ICompilationUnit, IJavaProject)} for an explanation
 * about the behavior of the refactoring computer. </p>
 * <p>
 * Note that {@link #filterStringNodes(List)} and {@link #computeReplaceEdit(ICompilationUnit, ArrayList, IASTNode)} needs to be implemented. </p>
 * 
 * @author Robert Heimbach, Maksim Melnik
 *
 */
public abstract class AbstractRefactoringComputer implements
        IRefactoringComputer {
    
    /**
     * Computes the text changes which need to be done to JML code by finding
     * all JML comments in the file, filtering those and computing the changes.
     * 
     * @param unit
     *            {@link ICompilationUnit} for which to create the changes.
     * @param project
     *            Project of the compilation unit.
     * @return List of edits which need to be done
     * @throws JavaModelException
     *             Thrown when the source file cannot be loaded from
     *             {@link ICompilationUnit} or he JMLcomments could not be received.
     */
    public final ArrayList<ReplaceEdit> computeNeededChangesToJML(
            ICompilationUnit unit, IJavaProject project) throws JavaModelException {

        final ArrayList<ReplaceEdit> changesToMake = new ArrayList<ReplaceEdit>();

        // Look through the JML comments and find the potential references which might need to be renamed
        final String source = unit.getSource();
        final CommentLocator loc = new CommentLocator(source);

        // Get all JML comments
        for (final CommentRange range : loc.findJMLCommentRanges()) {

            // Filter the comments
            final List<IASTNode> foundReferences = getReferencesInJMLcomments(project,
                    source, range);

            for (final IASTNode node : foundReferences) {

                computeReplaceEdit(unit, changesToMake, node);
            }
        }
        return changesToMake;
    }

    /**
     * Creates the text change for a given JML comment and adds the change to changesToMake.
     * 
     * @param changesToMake list to add the {@link ReplaceEdit}s to.
     * @param node {@link IASTNode} to compute the change for.
     */
    abstract protected void computeReplaceEdit(ICompilationUnit unit, ArrayList<ReplaceEdit> changesToMake,
            IASTNode node);

    /**
     * Searches through a given {@link CommentRange} in a source file and returns 
     * all JML comments as a list which is potentially empty.
     * 
     * @param project
     *            {@link IJavaProject} the source file resides in. 
     *            Needed to get the project specific active JMLProfile on which a {@link IJMLParser} is created.
     * @param source
     *            String representation of the source file to be used in the {@link IJMLParser}.
     * @param range
     *            CommentRange to be parsed. Specifies the location in the source file to be checked for JML comments.
     * @return List of found JML comments, represented as {@link IASTNode}s. Potentially empty if a ParserException was thrown or no comment could be found.
     * @throws JavaModelException
     *             Could not access source of given ICompilationUnit
     */
    private final List<IASTNode> getReferencesInJMLcomments(IJavaProject project,
            String source, CommentRange range) {
        
        List<IASTNode> stringNodes = new ArrayList<IASTNode>();
        
        // Get the project specific active JML profile and create a JML parser for it.
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
            return new ArrayList<IASTNode>();
        }
        
        // Filter the nodes by finding all strings which match the old name of the element to be renamed.
        final List<IStringNode> filteredStringNodes =  filterStringNodes(stringNodes);
        
        // For those occurrences left, find the primary nodes which provide the needed context for resolving.
        final List<IASTNode> primaries = getPrimaryNodes(filteredStringNodes, parseResult, !(activeProfile.getIdentifier().equals("org.key_project.jmlediting.profile.key")));
        
        return primaries;
    }

    /**
     * Returns the primary nodes for a given list of string nodes using the context information
     * of the parse result. 
     * 
     * @param stringNodes list of {@link IStringNode}s for which the corresponding primary nodes should be returned.
     * @param parseResult An {@link IASTNode} containing the parse result, i.e. the JML comments in the compilation unit. 
     * @param notKeYProfile boolean: true if the KeY-JML Profile is no used.
     * @return list of {@link IASTNode}s of primary node type.
     */
    private List<IASTNode>getPrimaryNodes(final List<IStringNode> stringNodes, final IASTNode parseResult, final boolean notKeYProfile){
        final List<IASTNode> primaries = new ArrayList<IASTNode>();
        
        for (final IStringNode stringNode: stringNodes) {       
          final IASTNode primary = getPrimaryNode(parseResult, stringNode, notKeYProfile);
          // nested expressions would add the same primary twice, e.g. if code looks like this:
          // TestClass test;
          // /*@ ensures this.test.test ... @*/
          if (!primaries.contains(primary))
              primaries.add(primary);  
        }
        return primaries;
    }

    /**
     * This method traverses the JML comment, saved as a {@link IASTNode} to find the 
     * primary node of a given {@link IStringNode}. 
     * 
     * @param context JML comment which provides the necessary context.
     * @param toTest string node to find the primary node for.
     * @param notKeYProfile boolean: true if the KeY profile is not used.
     * @return the primary node of the given string node.
     */
    private IASTNode getPrimaryNode(final IASTNode context, final IStringNode toTest, final boolean notKeYProfile) {
        return context.traverse(new INodeTraverser<IASTNode>() {

            @Override
            public IASTNode traverse(final IASTNode node, IASTNode existing) {
                if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
                    if(node.containsOffset(toTest.getStartOffset())) {
                        if(existing == null) {
                            existing = node;
                        } 
                        else if(node.getEndOffset() - node.getStartOffset() < existing.getEndOffset() - existing.getStartOffset()) {
                            existing = node;
                            return node;
                        }
                    }
                }
                // If the KeY Profile is not used, the primary node from the assignable node
                // cannot be found. In that case the primary node is the string node itself.
                if (notKeYProfile && existing == null){
                    return toTest;
                }     
                else
                    return existing;
            }        
        }, null);
    }

    /**
     * Filters a list of {@link IASTNode} for those which potentially reference 
     * the element to be renamed by comparing the name.
     * @param nodesList list to filter. Should be a list of IStringNodes.
     * @return filtered list
     */
    protected abstract List<IStringNode> filterStringNodes(final List<IASTNode> nodesList);
}
