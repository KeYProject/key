package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * Class which defines a constructor for the move refactoring computer which saves
 * the old and new fully qualified name of the element to be moved and how changes, 
 * in particular {@link ReplaceEdit}s, are computed.
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

        final int startOffset = node.getStartOffset();
        
        // check if it is fully qualified
        String newClassName = newClassFullQualName.substring(newClassFullQualName.lastIndexOf('.')+1);
        String oldClassName = oldClassFullQualName.substring(oldClassFullQualName.lastIndexOf('.')+1);

        IASTNode innerNode = node.getChildren().get(0).getChildren().get(0);
        if (innerNode instanceof IStringNode && 
                ((IStringNode) innerNode).getString().equals(oldClassName)) {
            changesToMake.add(new ReplaceEdit(startOffset, oldClassName.length(), newClassName));
        }
        else {
            final int length = oldClassFullQualName.length();
            changesToMake.add(new ReplaceEdit(startOffset, length, newClassFullQualName));
        }
    }
    
    /**
     * Returns the old fully qualified name.
     * @return The fully qualified name of the element to be moved.
     */
    protected final String getOldFullQualName() {
        return oldClassFullQualName;
    }
}
