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
public class ClassMoveRefactoringComputer extends
        AbstractMoveRefactoringComputer {

    private String fOldFullQualName;
    
    /**
     * 
     * @param fOldPackName
     * @param fNewPackName
     * @param fOldFullQualName
     */
    public ClassMoveRefactoringComputer(String fOldPackName, String fNewPackName, String fOldFullQualName) {
        super(fOldPackName, fNewPackName);
        this.fOldFullQualName = fOldFullQualName;
    }

    protected final List<IStringNode> filterStringNodes(List<IASTNode> nodesList) {
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        String nodeString="";

        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;
            if(fOldFullQualName.contains(stringNode.getString()))nodeString=nodeString+stringNode.getString();
            else nodeString="";
            if (nodeString.equals(fOldFullQualName)) {
                filteredList.add(stringNode);
            }
        }
        return filteredList;
    }
}
