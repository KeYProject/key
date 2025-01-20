/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.util.List;

import recoder.Service;
import recoder.bytecode.ClassFile;

/**
 * Retrieval and storage of parsed bytecode files.
 *
 * @author AL
 * @author RN
 */
public interface ClassFileRepository extends Service {

    /**
     * Returns the location of the class file for the given class or <tt>null</tt> if the file could
     * not be located.
     *
     * @param classname the name of the class for which the class should be located.
     * @return the class file location.
     */
    DataLocation findClassFile(String classname);

    /**
     * Retrieves the ClassFile for the compilation unit, in which the class with the given name is
     * located.
     *
     * @param classname the fully qualified classname of the required class.
     * @return the ClassFile for that class, if sources are available, <tt>null</tt> otherwise.
     */
    ClassFile getClassFile(String classname);

    /**
     * Returns a list of currently known class files.
     *
     * @return a list of known class files.
     * @since 0.72
     */
    List<ClassFile> getKnownClassFiles();

}
