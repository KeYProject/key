package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.text.edits.ReplaceEdit;

/**
 * Interface of a Refactoring Computer. Such a class computes all the changes which need to be
 * done to the JML annotations of a given java source file.
 * 
 * @author Robert Heimbach
 *
 */
public interface IRefactoringComputer {

   /**
    * Method which computes the needed changes to the JML annotations of a given java source
    * file.
    * 
    * @param unit {@link ICompilationUnit} we want to compute the changes for.
    * @param project {@link IJavaProject} the compilation unit resides in.
    * @return An {@link ArrayList} of {@link ReplaceEdit}s to the text of the compilation
    *         unit.
    * @throws JavaModelException Thrown if the compilation unit or the project cannot be
    *            accessed as intended.
    */
   public ArrayList<ReplaceEdit> computeNeededChangesToJML(final ICompilationUnit unit,
         final IJavaProject project) throws JavaModelException;
}
