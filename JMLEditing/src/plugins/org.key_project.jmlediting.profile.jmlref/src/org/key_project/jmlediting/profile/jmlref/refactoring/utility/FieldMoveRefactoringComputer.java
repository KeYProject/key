package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * 
 * @author Maksim Melnik
 *
 */
public class FieldMoveRefactoringComputer extends
        DefaultMoveRefactoringComputer {

    String fieldName;
    
    /**
     * 
     * @param oldClassFullQualName
     * @param newClassFullQualName
     * @param fieldName
     */
    public FieldMoveRefactoringComputer(String oldClassFullQualName,
            String newClassFullQualName, String fieldName) {
        super(oldClassFullQualName, newClassFullQualName);
        this.fieldName = fieldName;
    }

    protected List<IStringNode> filterStringNodes(List<IASTNode> nodesList) {
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        String nodeString="";

        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;
            if((oldClassFullQualName+"."+fieldName).contains(stringNode.getString()))nodeString=nodeString+stringNode.getString();
            else nodeString="";
            if (nodeString.equals(oldClassFullQualName+"."+fieldName)) {
                filteredList.add(stringNode);
            }
        }

        return filteredList;
    }

}
