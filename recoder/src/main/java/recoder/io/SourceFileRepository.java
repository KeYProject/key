/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.io.FilenameFilter;
import java.io.IOException;
import java.util.List;

import recoder.ParserException;
import recoder.Service;
import recoder.java.CompilationUnit;
import recoder.util.ProgressListener;

/**
 * Retrieval, storage and write back of abstract syntax trees.
 *
 * @author RN
 * @author AL
 */
public interface SourceFileRepository extends Service {

    /**
     * Returns the list of compilation unit in the project. This call may trigger an update.
     */
    List<CompilationUnit> getCompilationUnits();

    /**
     * Returns the current list of compilation unit in the repository.
     */
    List<CompilationUnit> getKnownCompilationUnits();

    /**
     * Returns the location of the source file for the given class or <tt>null</tt> if the file
     * could not be located.
     *
     * @param classname the name of the class for which the source should be located.
     * @return the source file location.
     */
    DataLocation findSourceFile(String classname);

    /**
     * Retrieves the AST for the compilation unit containing the class with the given name. This
     * method will not throw ParserExceptions, but pass these to the system error handler.
     *
     * @param classname the fully qualified classname of the required class.
     * @return the AST for that class, if sources are available, <tt>null</tt> otherwise.
     */
    CompilationUnit getCompilationUnit(String classname);

    /**
     * Retrieves the abstract syntax tree for the compilation unit within the specified file. The
     * service guarantees not to retrieve two different syntax trees for the same location. The
     * given filename may also be absolute - it will then be shortened if a prefix is in the search
     * path, or used to load the file regardless of the search path, otherwise.
     *
     * @param filename the name of the file to look for
     * @return a compilation unit object for that file, or <CODE>null</CODE> if there was no unit
     *         under this name whatoever.
     * @throws ParserException if something happened while parsing.
     */
    CompilationUnit getCompilationUnitFromFile(String filename) throws ParserException;

    /**
     * Calls {@link #getCompilationUnitFromFile}for all given file names.
     *
     * @param filenames the names of the files to look for.
     * @return a list of all available compilation units for the given files.
     * @throws ParserException if something happened while parsing.
     * @since 0.72
     */
    List<CompilationUnit> getCompilationUnitsFromFiles(String[] filenames) throws ParserException;

    /**
     * Retrieves all compilation units from the current search path, transitively. This is useful to
     * create a closed world, but assumes that all subdirectories of the search path belong to the
     * project.
     *
     * @return the list of all compilation units accessible via the search path.
     */
    List<CompilationUnit> getAllCompilationUnitsFromPath() throws ParserException;

    /**
     * Retrieves compilation units from the current search path, as given by the filter. The
     * algorithm checks all files in all subdirectories, but this can be narrowed down in the
     * filter.
     *
     * @param filter a filename filter accepting source files.
     * @return the list of all compilation units obeying the filter and accessible via the search
     *         path.
     */
    List<CompilationUnit> getAllCompilationUnitsFromPath(FilenameFilter filter)
            throws ParserException;

    /**
     * Checks if the given compilation unit is up to date or if it has changed after the last
     * persistant state.
     *
     * @param cu a compilation unit.
     * @return true if the compilation unit does not have to be written back.
     */
    boolean isUpToDate(CompilationUnit cu);

    /**
     * Print back the compilation unit to it's data location. If the compilation unit is still at
     * its original location, apply the filename mapper.
     */
    void print(CompilationUnit cu) throws IOException;

    /**
     * Print back all compilation units to their data locations. Can be used to print all units, or
     * only those that are not up to date.
     *
     * @param always flag to indicate whether all units should be written back ( <CODE>true</CODE>),
     *        or only these which are not up to date ( <CODE>false</CODE>).
     * @see #print
     * @see #isUpToDate
     */
    void printAll(boolean always) throws IOException;

    /**
     * Deletes all superfluous (renamed, detached) compilation unit files. Does not remove source
     * files from other sources.
     */
    void cleanUp();

    /**
     * Adds a progress listener for {@link #getAllCompilationUnitsFromPath},
     * {@link #getCompilationUnitsFromFiles}and {@link #printAll}.
     *
     * @param l a progress listener.
     * @since 0.72
     */
    void addProgressListener(ProgressListener l);

    /**
     * Removes the given progress listener.
     *
     * @param l a progress listener.
     * @since 0.72
     */
    void removeProgressListener(ProgressListener l);

}
