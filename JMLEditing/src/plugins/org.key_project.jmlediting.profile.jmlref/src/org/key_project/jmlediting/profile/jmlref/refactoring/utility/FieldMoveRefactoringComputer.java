package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * Class to compute the changes which needs to be done to the JML annotations 
 * if a static field is moved. In particular, it specifies how the list of nodes is 
 * filtered, i.e. how the JML expression to be replaced is found.
 * 
 * @author Maksim Melnik
 *
 */
public class FieldMoveRefactoringComputer extends
        AbstractMoveRefactoringComputer {

    private String fieldName;
    
    /**
     * Constructor. Saves the fully qualified name of the classes the field should be moved from and moved
     * to as well as the name of the field to be moved.
     *  
     * @param oldClassFullQualName fully qualified name of the class the field is in.
     * @param newClassFullQualName fully qualified name of the class the field should be moved to.
     * @param fieldName name of the field to be moved.
     */
    public FieldMoveRefactoringComputer(String oldClassFullQualName,
            String newClassFullQualName, String fieldName) {
        super(oldClassFullQualName, newClassFullQualName);
        this.fieldName = fieldName;
    }

    /**
     * Filters a list of {@link IASTNode} to exclude JML expression which does not need to be changed.
     * 
     * @param nodesList a list to be filtered. {@link IStringNode}s are expected.
     * @return list of filtered {@link IStringNode}s.
     */
    protected final List<IStringNode> filterStringNodes(List<IASTNode> nodesList) {
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        String nodeString="";

        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;
            
            // combine the string nodes
            if((getOldFullQualName()+"."+fieldName).contains(stringNode.getString()))
                nodeString=nodeString+stringNode.getString();
            // reset
            else nodeString="";
            
            if (nodeString.equals(getOldFullQualName()+"."+fieldName)) {
                filteredList.add(stringNode);
            }
        }
        return filteredList;
    }
}
