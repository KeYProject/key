package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.eclipse.text.edits.TextEdit;
import org.key_project.util.jdt.JDTUtil;

/**
 * A utility class to gather common methods used by some of the refactoring participants.
 * 
 * @author Robert Heimbach
 */
public class RefactoringUtil {

   /**
    * Returns all {@link IPackageFragment}s containing java source files from a given
    * {@link IJavaProject}.
    * 
    * @param project Project to get the package fragments from.
    * @return Package fragments containing java source files.
    * @throws JavaModelException Thrown if either the {@link IPackageFragmentRoot}s cannot be
    *            returned by the project or the children cannot be returned by the fragment
    *            root.
    */
   public static ArrayList<IPackageFragment> getAllPackageFragmentsContainingSources(
         final IJavaProject project) throws JavaModelException {

      ArrayList<IPackageFragment> allFragments = new ArrayList<IPackageFragment>();

      List<IPackageFragmentRoot> roots = JDTUtil.getSourcePackageFragmentRoots(project);

      // Iterate through the fragment roots to get all package fragments.
      for (IPackageFragmentRoot root : roots) {
         for (IJavaElement child : root.getChildren()) {
            allFragments.add((IPackageFragment) child); // guaranteed to be package fragments
         }
      }
      return allFragments;
   }

   /**
    * Fills a given {@link ArrayList} with {@link IJavaProject}s which all require the given
    * {@code refactoringStartingProject}.
    * 
    * @param projectsToCheck ArrayList of projects to fill.
    * @param refactoringStartingProject Given project for which we search in the required
    *           project list of the other projects.
    * @throws JavaModelException Thrown if either the list of all Java Projects cannot be
    *            returned or the required project names cannot be accessed for any project.
    */
   public static ArrayList<IJavaProject> getAllProjectsToCheck(
         ArrayList<IJavaProject> projectsToCheck, IJavaProject refactoringStartingProject)
         throws JavaModelException {

      // Iterate through all java projects and check for projects which require the active
      // project
      IJavaProject[] allProjects = JDTUtil.getAllJavaProjects();

      for (IJavaProject project : allProjects) {

         String[] requiredProjectNames = project.getRequiredProjectNames();

         if (requiredProjectNames.length > 0) {

            // check if the active project is in the list of the required projects of the
            // project
            // in the current iteration.
            for (String requiredProject : requiredProjectNames) {

               if (requiredProject.equals(refactoringStartingProject.getElementName())) {
                  if (!projectsToCheck.contains(project)) {
                     projectsToCheck.add(project);
                  }
               }
            }
         }
      }

      return projectsToCheck;
   }

   /**
    * Get a list of all classes in a given package, including all subpackages.
    * 
    * @param pack {@link IPackageFragment} we want the classes from.
    * @return ArrayList of Strings of all the fully qualified class names.
    * @throws JavaModelException Thrown when the compilation units of the given package cannot
    *            be returned.
    */
   public static ArrayList<String> getAllQualifiedNamesOfClasses(IPackageFragment pack)
         throws JavaModelException {
      ArrayList<String> allQualifiedNames = new ArrayList<String>();

      String packageName = pack.getElementName();

      // Get all class names, including classes in the subpackages.
      // Those have subpackage.className.java as name.
      ICompilationUnit[] compilationUnits = pack.getCompilationUnits();

      // Combine the package name with the class names.
      for (ICompilationUnit unit : compilationUnits) {

         String className = unit.getElementName();

         // without the .java
         allQualifiedNames.add(packageName + "."
               + className.substring(0, className.lastIndexOf('.')));
      }

      return allQualifiedNames;
   }

   /**
    * Given a possible empty list of changes, the return object for the refactoring
    * participants is determined and returned.
    * 
    * @param textFileChanges A potentially empty list of {@link TextFileChange}s.
    * @return null if the list is empty. One change object if the list has one element or a
    *         {@link CompositeChange} comprising all the elements in the list.
    */
   public static Change assembleChangeObject(ArrayList<TextFileChange> textFileChanges) {
      // Return null if only shared changes, otherwise gather changes to JML for classes with
      // no java changes.
      if (textFileChanges.isEmpty())
         return null;
      else if (textFileChanges.size() == 1) {
         return textFileChanges.get(0);
      }
      // Create a composite change to gather all the changes (effect in preview: a tree item
      // one level higher without preview is added)
      else {
         CompositeChange compositeChange = new CompositeChange("Changes to JML");
         for (TextFileChange change : textFileChanges) {
            compositeChange.add(change);
         }
         return compositeChange;
      }
   }

   /**
    * Combines a list of {@link ReplaceEdit}s to a {@link TextFileChange} for a given
    * {@link IFile}.
    * 
    * @param unit {@link ICompilationUnit} defining the file for which the change is.
    * @param editsToCombine list of edits.
    * @return the {@link TextFileChange} comprising all the {@link ReplaceEdit}s of the given
    *         list.
    * @throws JavaModelException thrown if the resource corresponding to the compilation unit
    *            could not be found.
    */
   public static TextFileChange combineEditsToChange(final ICompilationUnit unit,
         final ArrayList<ReplaceEdit> editsToCombine) throws JavaModelException {
      TextFileChange tfChange = new TextFileChange("",
            (IFile) unit.getCorrespondingResource());

      // Gather all the edits to the text (JML annotations) in a MultiTextEdit
      MultiTextEdit allEdits = combineEditsToMultiEdit(editsToCombine);

      tfChange.setEdit(allEdits);
      return tfChange;
   }

   /**
    * Combines a list of {@link TextEdit}s into a {@link MultiTextEdit}.
    * 
    * @param editsToCombine The list of edits to combine.
    * @return The {@link MultiTextEdit} which combined all the edits in the given list.
    */
   public static MultiTextEdit combineEditsToMultiEdit(
         final ArrayList<ReplaceEdit> editsToCombine) {
      // Gather all the edits to the text (JML annotations) in a MultiTextEdit
      MultiTextEdit allEdits = new MultiTextEdit();

      for (final ReplaceEdit edit : editsToCombine) {
         allEdits.addChild(edit);
      }

      return allEdits;
   }
}
