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
 * 
 * @author Robert Heimbach, Maksim Melnik
 *
 */
public abstract class DefaultMoveRefactoringComputer implements
        IRefactoringComputer {

    String oldClassFullQualName;
    String newClassFullQualName;
    
    DefaultMoveRefactoringComputer(String oldClassFullQualName, String newClassFullQualName){
        this.oldClassFullQualName = oldClassFullQualName;
        this.newClassFullQualName = newClassFullQualName;
    }
    
    /**
     * Computes the text changes which need to be done to JML code by finding
     * all JML comments in the file and asking the resolver if it references the
     * java element which is to be renamed.
     * 
     * @param unit
     *            ICompilation unit for which to create the changes
     * @param project
     *            Project of the compilation unit
     * @return List of edits which need to be done
     * @throws JavaModelException
     *             Thrown when the source file cannot be loaded from
     *             ICompilationUnit or he JMLcomments could not be received
     */
    public ArrayList<ReplaceEdit> computeNeededChangesToJML(
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
     * @param changesToMake
     * @param node
     */
    protected void computeReplaceEdit(ArrayList<ReplaceEdit> changesToMake,
            IASTNode node) {

        IASTNode changeThisNode = node;
        changeThisNode = node.getChildren().get(0).getChildren().get(0);

        final int startOffset = changeThisNode.getStartOffset();
        final int length = oldClassFullQualName.length();

        changesToMake.add(new ReplaceEdit(startOffset, length, newClassFullQualName));
        
    }

    /**
     * Searches through a given CommentRange in a source file and returns 
     * all JML comments as a potentially empty List.
     * 
     * @param project
     *            IJavaProject the unit resides in. Needed to get active JMLProfile for
     *            parser
     * @param source
     *            String representation of the source file to be used in the {@link IJMLParser}
     * @param range
     *            CommentRange to be parsed
     * @return List of found JML comments
     * @throws JavaModelException
     *             Could not access source of given ICompilationUnit
     */
    protected List<IASTNode> getReferencesInJMLcomments(IJavaProject project,
            String source, CommentRange range) {
        List<IASTNode> stringNodes = new ArrayList<IASTNode>();

        final IJMLProfile activeProfile = JMLPreferencesHelper
                .getProjectActiveJMLProfile(project.getProject());
        final IJMLParser parser = activeProfile.createParser();
        IASTNode parseResult;
        try {
            parseResult = parser.parse(source, range);
            stringNodes = Nodes.getAllNodesOfType(parseResult, NodeTypes.STRING);
        }
        catch (final ParserException e) {
            return new ArrayList<IASTNode>();
        }

        final List<IStringNode> filtedStringNodes =  filterStringNodes(stringNodes);

        final List<IASTNode> primaries = getPrimaryNodes(filtedStringNodes, parseResult);

        return primaries;
    }

    protected List<IASTNode> getPrimaryNodes(final List<IStringNode> stringNodes, final IASTNode parseResult) {
        final List<IASTNode> primaries = new ArrayList<IASTNode>();
        
        for (final IStringNode stringNode: stringNodes) {       
            final IASTNode primary = getPrimaryNode(parseResult, stringNode);
            primaries.add(primary);  
        }
        return primaries;
    }

    protected IASTNode getPrimaryNode(final IASTNode context, final IStringNode toTest) {
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

}
