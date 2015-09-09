package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
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
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolveResultType;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/**
 * The default refactoring computer to compute changes to the JML annotations when a 
 * renaming was done by calling the method {@link #computeNeededChangesToJML(ICompilationUnit, IJavaProject)}. 
 * 
 * @author Robert Heimbach
 */
public class DefaultRenameRefactoringComputer implements IRefactoringComputer {

    private Object fOldName;
    private Object fJavaElementToRename;
    private String fNewName;

    /**
     * Constructor of the refactoring computer. It needs to know the old and new name of
     * the element which is renamed and a reference to the element itself as a comparison
     * to check which elements in the JML annotations really refer to this element.
     * 
     * @param fJavaElementToRename Element which is renamed.
     * @param fOldName Old name of the element which is renamed.
     * @param fNewName New name of the element which is renamed.
     */
    public DefaultRenameRefactoringComputer(IJavaElement fJavaElementToRename,
            String fOldName, String fNewName) {
        super();
        this.fOldName = fOldName;
        this.fJavaElementToRename = fJavaElementToRename;
        this.fNewName = fNewName;
    }

    /**
     * Computes the text changes which need to be done to JML code by finding
     * all JML comments in a java source file, filtering those based on the old name of the 
     * element which is renamed and asking the resolver if those nodes left are references to the
     * java element which is to be renamed.
     * 
     * @param unit
     *            {@link ICompilationUnit} for which to create the changes
     * @param project
     *           {@link IJavaProject} the compilation unit is in.
     * @return Array list of {@link ReplaceEdit}s which need to be done to the given source file.
     * @throws JavaModelException
     *             Thrown when the source file cannot be loaded from the compilation unit.
     */
    @Override
    public final ArrayList<ReplaceEdit> computeNeededChangesToJML(
            ICompilationUnit unit, IJavaProject project)
            throws JavaModelException {
        
        final ArrayList<ReplaceEdit> changesToMake = new ArrayList<ReplaceEdit>();

        // Look through the JML comments and find the potential references which might need to be renamed
        final String source = unit.getSource();
        final CommentLocator loc = new CommentLocator(source);

        // Get all JML comments
        for (final CommentRange range : loc.findJMLCommentRanges()) {

            // Filter the comments
            final List<IASTNode> potentialReferences = getPotentialReferencesInJMLcomments(project,
                    source, range);

            // Check with the help of the resolver which ones really need to change 
            // and create the changes by filling the changesToMake list.
            for (final IASTNode node : potentialReferences) {

                resolvePotentialReferences(unit, node, changesToMake);
            }
        }
        return changesToMake;
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
    private List<IASTNode> getPotentialReferencesInJMLcomments(final IJavaProject project, final String source, final CommentRange range) {

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
        
        // Filter the nodes by finding all strings which match the old name of the element to be renamed.
        final List<IStringNode> filteredStringNodes =  filterStringNodes(stringNodes);
        
        // For those occurrences left, find the primary nodes which provide the needed context for resolving.
        final List<IASTNode> primaries = getPrimaryNodes(filteredStringNodes, parseResult, !(activeProfile.getIdentifier().equals("org.key_project.jmlediting.profile.key")));
        
        return primaries;
    }

    /**
     * Filters a list of {@link IASTNode} for those which potentially reference 
     * the element to be renamed by comparing the string node to the old name of the element
     * to be renamed.
     * 
     * @param nodesList List to filter. Should be a list of {@link IStringNode}s.
     * @return filtered list of string nodes. Potentially empty.
     */
    private ArrayList<IStringNode> filterStringNodes(final List<IASTNode> nodesList) {
        
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        
        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;     
            if (stringNode.getString().equals(fOldName)) {     
                filteredList.add(stringNode);
            }
        }
        
        return filteredList;
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
     * This method traverses the jml comment, saved as a {@link IASTNode} to find the 
     * primary node of a given {@link IStringNode}. 
     * 
     * @param context jml comment which provides the necessary context.
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
     * Checks if a given {@link IASTNode} in a given {@link ICompilationUnit} references the
     * element to be renamed. Then the needed {@Link ReplaceEdit} is created and 
     * added to changesToMake.
     * 
     * @param unit
     *            The compilation unit the IASTNode is in.
     * @param node
     *            IASTNode of the primary expression type to resolve.
     * @param changesToMake
     *            Arraylist of {@link ReplaceEdit}s to accumulate the needed changes. 
     */
    private void resolvePotentialReferences(final ICompilationUnit unit, final IASTNode node, final ArrayList<ReplaceEdit> changesToMake) {
        
        final IASTNode nodeToChange = node;
    
        final IResolver resolver = new Resolver();
        ResolveResult result = null;
        try {
            
            result = resolver.resolve(unit, node);
            
            if (isReferencedElement(result)){
                computeReplaceEdit(changesToMake, nodeToChange);
            }
            
            // Needed to move through the node to inner nodes to get to the right place
            // to make the change / text edit.
            int i = 0;
            
            //if (result == null)
            //    i = 1;
                      
            while(resolver.hasNext()) { 
                 result = resolver.next();
                 
                 if (isReferencedElement(result)) {
                     // Access inner node which resolver checked by .next() method.
                    if (nodeToChange.getChildren().size() >= 1) {
                         
                        final IASTNode child = nodeToChange.getChildren().get(1);
                         
                        if (child.getChildren().size() >= i) {
                             final IASTNode innerNode = nodeToChange.getChildren().get(1).getChildren().get(i);
                             computeReplaceEdit(changesToMake, innerNode);
                         }
                    }    
                 }
                 // Go to the next expression in the list which need to be checked
                 if (result != null && result.getResolveType().equals(ResolveResultType.METHOD)){
                     // In case of a Method Call like in test().test, the whole method call has two list entries
                     // in the node. One for the name of the method and one for the arguments.
                     // Thus we need to skip two instead of one.
                     i = i + 2;
                 }
                 else {
                     i = i + 1;
                 }
            }
        }
        catch (final ResolverException e) {
            LogUtil.getLogger().logError(e);
        }
    }
    
    /**
     * Checks if the resolved result equals the element to be renamed.
     * 
     * @param result The {@link ResolveResult}.
     * @return true if the resolve result equals the element to be renamed. Falls otherwise.
     */
    private Boolean isReferencedElement(final ResolveResult result){
        if (result == null || result.getBinding() == null) {
            return false;
        }
        else
            return result.getBinding().getJavaElement().equals(fJavaElementToRename);
    }
    

    /**
     * Creates the text change and adds it to changesToMake.
     * 
     * @param changesToMake list of {@link ReplaceEdit}s to fill.
     * @param node the {@link IASTNode} which should be edited.
     */
    private void computeReplaceEdit(final ArrayList<ReplaceEdit> changesToMake,
            final IASTNode node) {

        IASTNode changeThisNode = node;
        
        if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
            changeThisNode = node.getChildren().get(0).getChildren().get(0);
        }
        
        // Keep the . when it is a member access like "this.field" instead of replacing it.
        if (node.getType() == ExpressionNodeTypes.MEMBER_ACCESS){
            changeThisNode = node.getChildren().get(1);
        }
        
        // compute the text location which needs to change.
        final int startOffset = changeThisNode.getStartOffset();
        final int length = changeThisNode.getEndOffset()
                - changeThisNode.getStartOffset();

        final ReplaceEdit edit = new ReplaceEdit(startOffset,
                length, fNewName);

        changesToMake.add(edit);
    }
}
