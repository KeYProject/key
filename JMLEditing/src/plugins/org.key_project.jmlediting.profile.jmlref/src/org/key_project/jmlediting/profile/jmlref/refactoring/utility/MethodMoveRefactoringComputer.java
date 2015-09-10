package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * Class to compute the changes which needs to be done to the JML annotations 
 * if a static method is moved. In particular, it specifies how the list of nodes is 
 * filtered, i.e. how the JML expression to be replaced is found.
 * 
 * @author Maksim Melnik
 *
 */
public class MethodMoveRefactoringComputer extends
        AbstractMoveRefactoringComputer {

    private String methName;
    
    /**
     * Constructor. Saves the fully qualified name of the classes the method should be moved from and moved to
     * as well as the name of the method to be moved.
     * 
     * @param oldClassFullQualName fully qualified name of the class the method to be moved is in.
     * @param newClassFullQualName fully qualified name of the class the method should be moved to.
     * @param methName name of the method to be moved.
     */
    public MethodMoveRefactoringComputer(String oldClassFullQualName,
            String newClassFullQualName, String methName) {
        super(oldClassFullQualName, newClassFullQualName );
        this.methName = methName;
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
            
            if((getOldFullQualName()+"."+methName).contains(stringNode.getString()))
                nodeString=nodeString+stringNode.getString();
            else nodeString="";
            
            if (nodeString.equals(getOldFullQualName()+"."+methName)) {
                filteredList.add(stringNode);
            }
        }
        return filteredList;
    }
}
