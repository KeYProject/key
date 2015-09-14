package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * Class to compute the changes which needs to be done to the JML annotations 
 * if a static field or method is moved. In particular, it specifies how the list of nodes is 
 * filtered, i.e. how the JML expression to be replaced is found.
 * 
 * @author Maksim Melnik
 *
 */
public class FieldAndMethodMoveRefactoringComputer extends
        AbstractMoveRefactoringComputer {

    private String elementName;
    
    /**
     * Constructor. Saves the fully qualified name of the classes the field/method should be moved from and moved
     * to as well as the name of the field/method to be moved.
     *  
     * @param oldClassFullQualName fully qualified name of the class the field/method is in.
     * @param newClassFullQualName fully qualified name of the class the field/method should be moved to.
     * @param elementName name of the field/method to be moved.
     */
    public FieldAndMethodMoveRefactoringComputer(String oldClassFullQualName,
            String newClassFullQualName, String elementName) {
        super(oldClassFullQualName, newClassFullQualName);
        this.elementName = elementName;
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
            if((getOldFullQualName()+"."+elementName).contains(stringNode.getString()))
                nodeString=nodeString+stringNode.getString();
            // reset
            else nodeString="";
            
            if (nodeString.equals(getOldFullQualName()+"."+elementName)) {
                filteredList.add(stringNode);
            }
        }
        
        // check for not fully qualified access but access via import statement
        String oldClassName = getOldFullQualName().substring(getOldFullQualName().lastIndexOf('.')+1);
        
        nodeString = "";
        for (final IASTNode node: nodesList) {
            final IStringNode stringNode = (IStringNode) node;
         
            // combine the string nodes
            if((oldClassName+"."+elementName).contains(stringNode.getString()))
                nodeString=nodeString+stringNode.getString();
            // reset
            else nodeString="";
            
            if (nodeString.equals(oldClassName+"."+elementName)) {
                int start = stringNode.getStartOffset();
                
                boolean isContained = false;
                for (IStringNode n : filteredList){
                    if (n.containsOffset(start))
                        isContained = true;
                }
                if (!isContained)
                    filteredList.add(stringNode);
            }
            
        }
        
        return filteredList;
    }
}
