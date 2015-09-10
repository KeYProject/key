package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * 
 * @author Maksim Melnik
 *
 */
public abstract class AbstractMoveRefactoringComputer extends AbstractRefactoringComputer {

    private String oldClassFullQualName;
    private String newClassFullQualName;

    /**
     * Constructor which saves the old and the new name. Usually in a fully qualified form.
     * 
     * @param oldClassFullQualName old fully qualified name of the element to be moved.
     * @param newClassFullQualName new fully qualified name of the element to be moved.
     */
    AbstractMoveRefactoringComputer(String oldClassFullQualName, String newClassFullQualName){
        this.oldClassFullQualName = oldClassFullQualName;
        this.newClassFullQualName = newClassFullQualName;
    }
    
    /**
     * Creates the text change and adds it to changesToMake.
     * 
     * @param changesToMake list to add the {@link ReplaceEdit}s to.
     * @param node {@link IASTNode} to compute the change for.
     */
    protected final void computeReplaceEdit(ICompilationUnit unit, ArrayList<ReplaceEdit> changesToMake,
            IASTNode node) {

        IASTNode changeThisNode = node;
        // all nodes of primary expression type. (no complicated member accesses or such)
        //changeThisNode = node.getChildren().get(0).getChildren().get(0);

        // compute the location of the text edit.
        final int startOffset = changeThisNode.getStartOffset();
        final int length = oldClassFullQualName.length();

        changesToMake.add(new ReplaceEdit(startOffset, length, newClassFullQualName));
        
    }
    
    /**
     * Returns the old fully qualified name.
     * @return The fully qualified name of the element to be moved.
     */
    protected final String getOldFullQualName() {
        return oldClassFullQualName;
    }
}
