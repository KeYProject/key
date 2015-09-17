package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolveResultType;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/**
 * The refactoring computer to compute changes to the JML annotations when a 
 * renaming was done by calling the method {@link #computeNeededChangesToJML(ICompilationUnit, IJavaProject)}.
 * <p>
 * The list of {@link IStringNode}s is filtered by comparing the Strings to the name of 
 * the element which is refactored. Filtering is important to reduce the number of times
 * the Resolver is called. </p>
 * <p>
 * The {@link ReplaceEdit}s are created by calling the {@link Resolver} and finding out if 
 * the JML expression / the {@link IASTNode} refers to the element to be refactored. Complex
 * expressions need to call the {@link Resolver.#next()} method and mimick the way the Resolver
 * traverses the expression. </p>
 * 
 * @author Robert Heimbach
 */
public class RenameRefactoringComputer extends AbstractRefactoringComputer {

    private Object fOldName;
    private Object fJavaElementToRename;
    private String fNewName;

    /**
     * Constructor of the rename refactoring computer. Additionally to the old and new name
     * of the element to be renamed it saves a reference to the element itself to check later
     * which elements in the JML annotations really refer to this element.
     * 
     * @param fJavaElementToRename Element which is renamed.
     * @param fOldName Old name of the element which is renamed.
     * @param fNewName New name of the element which is renamed.
     */
    public RenameRefactoringComputer(IJavaElement fJavaElementToRename,
            String fOldName, String fNewName) {
        this.fOldName = fOldName;
        this.fNewName = fNewName;
        this.fJavaElementToRename = fJavaElementToRename;
    }

    /**
     * Filters a list of {@link IASTNode} for those which potentially reference 
     * the element to be renamed by comparing the string node to the old name of the element
     * to be renamed.
     * 
     * @param nodesList List to filter. Should be a list of {@link IStringNode}s.
     * @return filtered list of string nodes. Potentially empty.
     */
    protected final ArrayList<IStringNode> filterStringNodes(final List<IASTNode> nodesList) {
        
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
     * Checks if a given {@link IASTNode} in a given {@link ICompilationUnit} references the
     * element to be renamed. Then the needed {@Link ReplaceEdit} is created and 
     * added to changesToMake.
     *
     * @param unit
     *            The compilation unit the IASTNode is in.
     * @param changesToMake
     *            Arraylist of {@link ReplaceEdit}s to accumulate the needed changes.
     * @param node
     *            IASTNode of the primary expression type to resolve.
     */
    @Override
    protected final void computeReplaceEdit(final ICompilationUnit unit, final ArrayList<ReplaceEdit> changesToMake, final IASTNode node) {
        
        final IASTNode nodeToChange = node;
    
        final IResolver resolver = new Resolver();
        ResolveResult result = null;
        try {
            
            result = resolver.resolve(unit, node);
            
            if (isReferencedElement(result)){
                createEditAndAddToList(changesToMake, nodeToChange);
            }
            
            // Complex expressions (e.g. method calls or member accesses) need to call 
            // the .next() method of the Resolver to move through the node to the inner node 
            // which is less complex
            
            // To move to the right place in the expression; usually saved as a list.
            int i = 0;
                      
            while(resolver.hasNext()) { 
                 result = resolver.next();
                 
                 if (isReferencedElement(result)) {
                     // Access inner node which resolver checked by .next() method.
                    if (nodeToChange.getChildren().size() >= 1) {
                         
                        final List<IASTNode> nodesToSelectFrom = nodeToChange.getChildren().get(1).getChildren();                      
                         
                        if (nodesToSelectFrom.size() > i) {
                             IASTNode selection = nodesToSelectFrom.get(i);
                             
                             // If it is a method call, get the next list item.
                             if (selection.getType() == ExpressionNodeTypes.METHOD_CALL_PARAMETERS){
                                 if (nodesToSelectFrom.size() > i+1)
                                     selection = nodesToSelectFrom.get(i+1);
                                 else {
                                     continue; // correct selection not possible
                                 }
                             }
                             createEditAndAddToList(changesToMake, selection);
                        }
                    }    
                 }
                 // Change i to have the correct starting place for the next call of resolver.next()
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
    private void createEditAndAddToList(final ArrayList<ReplaceEdit> changesToMake,
            final IASTNode node) {

        IASTNode changeThisNode = node;
        
        // Get the place to be edited in the JML comment / the node.
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
