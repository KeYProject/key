package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * Class to compute the changes which needs to be done to the JML annotations 
 * if a class is moved. In particular, it specifies how the list of nodes is 
 * filtered, i.e. how the JML expression to be replaced is found.
 * 
 * @author Maksim Melnik, Robert Heimbach
 *
 */
public class ClassMoveRefactoringComputer extends
        AbstractRefactoringComputer {

    private String fOldFullQualName;
    private String fOldPackName;
    private String fNewPackName;
    
    /**
     * Constructor, saves the source and the destination the class to be moved is in and the fully
     * qualified name of the class.
     * 
     * @param fOldPackName name of the package the class is in.
     * @param fNewPackName name of the package the class should be moved to.
     * @param fOldFullQualName fully qualified name / path of the class to be moved.
     */
    public ClassMoveRefactoringComputer(String fOldPackName, String fNewPackName, String fOldFullQualName) {
        this.fOldPackName = fOldPackName;
        this.fNewPackName = fNewPackName;
        this.fOldFullQualName = fOldFullQualName;
    }
    
    /**
     * Filters a list of {@link IASTNode} to exclude JML expression which does not need to be changed.
     * 
     * @param nodesList a list to be filtered. {@link IStringNode}s are expected.
     * @return list of filtered {@link IStringNode}s.
     */
    protected final List<IStringNode> filterStringNodes(List<IASTNode> nodesList) {
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        
        // Note that an expression like package.subpackage.Class is separated in three nodes.
        
        // To combine the expression
        String nodeString="";

        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;
            
            // combine the expression because the current String is contained in the string to replace.
            if(fOldFullQualName.contains(stringNode.getString()))
                nodeString=nodeString+stringNode.getString();
            // reset the expression
            else nodeString="";
            
            if (nodeString.equals(fOldFullQualName)) {
                filteredList.add(stringNode);
            }
        }
        return filteredList;
    }

    /**
     * Creates the text change and adds it to changesToMake.
     * 
     * @param changesToMake list to add the {@link ReplaceEdit}s to.
     * @param primaryStringMap {@link IASTNode} to compute the change for.
     */
    protected final void computeReplaceEdit(ICompilationUnit unit, ArrayList<ReplaceEdit> changesToMake,
            HashMap<IASTNode, List<IStringNode>> primaryStringMap) {

        for (IASTNode node : primaryStringMap.keySet()) {
        
            final int startOffset = node.getStartOffset();
            
            int length = fOldPackName.length();
            
            changesToMake.add(new ReplaceEdit(startOffset, length, fNewPackName));
        }
    }
}