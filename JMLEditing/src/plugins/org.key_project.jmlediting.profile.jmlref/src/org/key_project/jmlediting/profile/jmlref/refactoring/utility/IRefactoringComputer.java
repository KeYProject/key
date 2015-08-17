package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.text.edits.ReplaceEdit;

/**
 * 
 * @author Robert Heimbach
 *
 */
public interface IRefactoringComputer {

    public ArrayList<ReplaceEdit> computeNeededChangesToJML(
            final ICompilationUnit unit, final IJavaProject project) throws JavaModelException;
}
