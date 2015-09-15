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
@Deprecated
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
     * Returns the old fully qualified name.
     * @return The fully qualified name of the element to be moved.
     */
    protected final String getOldFullQualName() {
        return oldClassFullQualName;
    }
}
