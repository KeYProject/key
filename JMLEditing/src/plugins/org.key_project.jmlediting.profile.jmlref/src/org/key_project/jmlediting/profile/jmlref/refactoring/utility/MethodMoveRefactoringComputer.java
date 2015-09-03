package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * 
 * @author Robert Heimbach, Maksim Melnik
 *
 */
public class MethodMoveRefactoringComputer extends
        DefaultMoveRefactoringComputer {

    String methName;
    
    /**
     * 
     * @param oldClassFullQualName
     * @param newClassFullQualName
     * @param methName
     */
    public MethodMoveRefactoringComputer(String oldClassFullQualName,
            String newClassFullQualName, String methName) {
        super(oldClassFullQualName, newClassFullQualName);
        this.methName = methName;
    }

    protected List<IStringNode> filterStringNodes(List<IASTNode> nodesList) {
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        String nodeString="";

        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;
            if((oldClassFullQualName+"."+methName).contains(stringNode.getString()))nodeString=nodeString+stringNode.getString();
            else nodeString="";
            if (nodeString.equals(oldClassFullQualName+"."+methName)) {
                filteredList.add(stringNode);
            }
        }

        return filteredList;
    }

}
