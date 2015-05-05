// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;
import java.util.NoSuchElementException;

import recoder.io.DataLocation;

/**
 * This class encapsulates a collection of files which is arbitrarily organised.
 * It is iterable and allows to open all files (not directories) during the
 * iteration as streams.
 * 
 * Subclasses allow to iterate a jar/zip-file or a directory.
 * 
 * Typical usage:
 * 
 * <pre>
 *   FileCollection fc = ... ;
 *   FileCollection.Walker walker = fc.createWalker(".java");
 *   while(walker.step()) {
 *      // use the data of current location via walker.getCurrent...()
 *   }
 * </pre>
 * 
 * @author MU
 */

public interface FileCollection {

    /**
     * create a {@link Walker} object that allows to iterate the file
     * collection.
     * 
     * The search can be restricted to files with a certain extension. If this
     * is not desired, one specifies null for the extension.
     * 
     * @param extension
     *                file extension to be considered only. null if all files
     *                are to be considered.
     * @return a freshly created walker
     * @throws IOException
     *                 during opening resources
     */
    public Walker createWalker(String extension) throws IOException;

    /**
     * create a {@link Walker} object that allows to iterate the file
     * collection.
     * 
     * The search can be restricted to files with a certain extension. If this
     * is not desired, one specifies null for the extension.
     * 
     * @param extensions
     *                file extensions to be considered only. null if all files
     *                are to be considered.
     * @return a freshly created walker
     * @throws IOException
     *                 during opening resources
     */
    public Walker createWalker(String[] extensions) throws IOException;

    /**
     * A Walker allows to iterate (once and one way) through a FileCollection.
     */
    public interface Walker {

        /**
         * step to next element in the collection if there is another one. The
         * getCurrent...() functions will behave differently after a call to
         * step().
         * 
         * @return true iff there is another element in the collection
         */
        public boolean step();

        /**
         * get the name of the current file in the iteration. This is only the
         * short name not including any location data.
         * 
         * @return a short file name, not null
         * @throws NoSuchElementException if the previous call to step returned false.
         */
        public String getCurrentName() throws NoSuchElementException;
        
        /**
         * get a {@link DataLocation} object describing the current file.
         * The dynamic type of the result depends on the implementation in use.
         * 
         * @return a {@link DataLocation}, not null
         * @throws NoSuchElementException if the previous call to step returned false.
         */
        public DataLocation getCurrentDataLocation() throws NoSuchElementException;
        
        /**
         * return the type of the structure that is iterated. Must return the
         * same value for any call
         * 
         * @return a non-null String describing the type (e.g. "zip" or "file");
         * @throws NoSuchElementException if the previous call to step returned false.
         */
        public String getType();

        /**
         * create a new InputStream for the current element of the iteration. It
         * is in the user's obligation to close the stream after using it.
         * 
         * @return a freshly created InputStream, the dynamic type depends on
         *         the implementation
         * @throws IOException if the resource cannot be opened
         * @throws NoSuchElementException if the previous call to step returned false.
         */
        public InputStream openCurrent() throws IOException, NoSuchElementException;
    }
}