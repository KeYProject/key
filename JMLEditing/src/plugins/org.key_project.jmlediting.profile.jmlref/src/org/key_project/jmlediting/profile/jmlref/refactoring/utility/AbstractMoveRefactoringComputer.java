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
 * in contrast to {@link DefaultRenameRefactoringComputer} changes are directly
 * done to the found and filtered JML nodes and easier to compute. </p>
 * <p>
 * See {@link #computeNeededChangesToJML(ICompilationUnit, IJavaProject)} for an explanation
 * about the behavior of the refactoring computer. </p>
 * <p>
 * Note that {@link #filterStringNodes(List)} needs to be implemented. </p>
 * 
 * @author Robert Heimbach, Maksim Melnik
 *
 */
public abstract class AbstractMoveRefactoringComputer implements
        IRefactoringComputer {

    private String oldClassFullQualName;
    private String newClassFullQualName;

    /**
     * Constructor which saves the old and the new name. Usually in a fully qualified form.
     * @param oldClassFullQualName old name of the element to be moved.
     * @param newClassFullQualName new name of the element to be moved.
     */
    AbstractMoveRefactoringComputer(String oldClassFullQualName, String newClassFullQualName){
        this.setOldClassFullQualName(oldClassFullQualName);
        this.newClassFullQualName = newClassFullQualName;
    }
    
    /**
     * Computes the text changes which need to be done to JML code by finding
     * all JML comments in the file, filtering those and compute the changes
     * for the nodes which are still left.
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

        // Look through the JML comments and find the potential references which need to be renamed
        final String source = unit.getSource();
        
        final CommentLocator loc = new CommentLocator(source);

        for (final CommentRange range : loc.findJMLCommentRanges()) {
            final List<IASTNode> foundReferences = getReferencesInJMLcomments(project,
                    source, range);

            for (final IASTNode node : foundReferences) {
                computeReplaceEdit(changesToMake, node);
            }
        }
        return changesToMake;
    }

    /**
     * Creates the text change and adds it to changesToMake.
     * 
     * @param changesToMake list to add the {@link ReplaceEdit}s to.
     * @param node {@link IASTNode} to compute the change for.
     */
    private final void computeReplaceEdit(ArrayList<ReplaceEdit> changesToMake,
            IASTNode node) {

        IASTNode changeThisNode = node;
        // all nodes of primary expression type. (no complicated member accesses or such)
        //changeThisNode = node.getChildren().get(0).getChildren().get(0);

        // compute the location of the text edit.
        final int startOffset = changeThisNode.getStartOffset();
        final int length = getOldClassFullQualName().length();

        changesToMake.add(new ReplaceEdit(startOffset, length, newClassFullQualName));
        
    }

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

        // Get the project specific active JML profile and create a jml parser for it.
        final IJMLProfile activeProfile = JMLPreferencesHelper
                .getProjectActiveJMLProfile(project.getProject());
        final IJMLParser parser = activeProfile.createParser();
        IASTNode parseResult;
        try {
            // Get the jml comments in the given range as string nodes.
            parseResult = parser.parse(source, range);
            stringNodes = Nodes.getAllNodesOfType(parseResult, NodeTypes.STRING);
        }
        catch (final ParserException e) {
            return new ArrayList<IASTNode>();
        }

        // Filter the nodes (exact way needs to be specified by implementing the abstract method)
        final List<IStringNode> filteredStringNodes =  filterStringNodes(stringNodes);
        
        // For those occurrences left, find the primary nodes.
        final List<IASTNode> primaries = getPrimaryNodes(filteredStringNodes, parseResult);

        return primaries;
    }

    private final List<IASTNode> getPrimaryNodes(final List<IStringNode> stringNodes, final IASTNode parseResult) {
        final List<IASTNode> primaries = new ArrayList<IASTNode>();
        
        for (final IStringNode stringNode: stringNodes) {       
            final IASTNode primary = getPrimaryNode(parseResult, stringNode);
            primaries.add(primary);  
        }
        return primaries;
    }

    private final IASTNode getPrimaryNode(final IASTNode context, final IStringNode toTest) {
        return context.traverse(new INodeTraverser<IASTNode>() {

            @Override
            public IASTNode traverse(final IASTNode node, IASTNode existing) {
                if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
                    if(node.containsOffset(toTest.getStartOffset())) {
                        if(existing == null) {
                            existing = node;
                        } else if(node.getEndOffset() - node.getStartOffset() < existing.getEndOffset() - existing.getStartOffset()) {
                            existing = node;
                            return node;
                        }
                    }
                }
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

    public final String getOldClassFullQualName() {
        return oldClassFullQualName;
    }

    public final void setOldClassFullQualName(String oldClassFullQualName) {
        this.oldClassFullQualName = oldClassFullQualName;
    }

}
