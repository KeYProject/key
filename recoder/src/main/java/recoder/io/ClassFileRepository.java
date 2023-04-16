// This file is part of the RECODER library and protected by the LGPL.

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
