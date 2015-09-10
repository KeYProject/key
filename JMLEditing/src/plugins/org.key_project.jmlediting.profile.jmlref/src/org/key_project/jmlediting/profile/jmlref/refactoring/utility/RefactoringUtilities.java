package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.util.jdt.JDTUtil;

/**
 * A utility class to gather common methods used by some of the refactoring participants.
 * 
 * @author Robert Heimbach
 */
public class RefactoringUtilities {

    /**
     * Returns all {@link IPackageFragment}s containing java source files from a given {@link IJavaProject}.
     * 
     * @param project Project to get the package fragments from.
     * @return Package fragments containing java source files.
     * @throws JavaModelException Thrown if either the {@link IPackageFragmentRoot}s cannot be returned
     *          by the project or the children cannot be returned by the fragment root.
     */
    public static ArrayList<IPackageFragment> getAllPackageFragmentsContainingSources(final IJavaProject project) throws JavaModelException {
        
        ArrayList<IPackageFragment> allFragments = new ArrayList<IPackageFragment>();
        
        IPackageFragmentRoot[] roots = project.getPackageFragmentRoots();
        
        // Checks each roots if it contains source/class files (i.e. it is no archive) 
        for (IPackageFragmentRoot root: roots){
            if (!root.isArchive()) {
                IJavaElement[] children = root.getChildren();            
                for (IJavaElement child: children){
                    if (child.getElementType() == IJavaElement.PACKAGE_FRAGMENT)
                        allFragments.add((IPackageFragment)child);
                }
            }
        }     
        return allFragments;
    }
    
    /**
     * Fills a given ArrayList with {@link IJavaProject}s which need to be checked in the refactoring
     * because they all require the given project and thus can reference any class of that given project.
     * 
     * @param projectsToCheck ArrayList of IJavaProjects to fill.
     * @param refactoringStartingProject Given project for which we search in the required project list of the other projects.
     * @throws JavaModelException Thrown if either the list of all Java Projects cannot be returned or the required project 
     *          names cannot be accessed for any project.
     */
    public static void getAllProjectsToCheck(ArrayList<IJavaProject> projectsToCheck, IJavaProject refactoringStartingProject)
            throws JavaModelException {
        
        // Iterate through all java projects and check for projects which require the active project
        IJavaProject[] allProjects = JDTUtil.getAllJavaProjects();
        
        for (IJavaProject project: allProjects){
            
            String[] requiredProjectNames = project.getRequiredProjectNames();
            
            if (requiredProjectNames.length > 0) {
                
                // check if the active project is in the list of the required projects of the project
                // in the current iteration.
                for (String requiredProject: requiredProjectNames){
                    
                    if (requiredProject.equals(refactoringStartingProject.getElementName())) {
                        projectsToCheck.add(project);
                    }
                } 
            }
        }
    }

    /**
     * Get a list of all classes in a given package, including all subpackages.
     * 
     * @param pack {@link IPackageFragment} we want the classes from.
     * @return ArrayList of Strings of all the fully qualified class names.
     * @throws JavaModelException Thrown when the compilation units of the given package cannot be returned.
     */
    public static ArrayList<String> getAllQualifiedNamesOfClasses(IPackageFragment pack) throws JavaModelException {
        ArrayList<String> allQualifiedNames = new ArrayList<String>();
        
        String packageName = pack.getElementName();
        
        // Get all class names, including classes in the subpackages. 
        // Those have subpackage.className.java as name.
        ICompilationUnit[] compilationUnits = pack.getCompilationUnits();
        
        // Combine the package name with the class names.
        for (ICompilationUnit unit : compilationUnits){
            
            String className = unit.getElementName();
            
            // without the .java
            allQualifiedNames.add(packageName + "." + className.substring(0, className.lastIndexOf('.')));
        }
        
        return allQualifiedNames;
    }
}
