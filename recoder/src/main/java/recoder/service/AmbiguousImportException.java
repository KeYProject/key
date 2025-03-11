/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.ArrayList;
import java.util.List;

import recoder.ModelException;
import recoder.abstraction.ClassType;
import recoder.java.Import;

/**
 * Exception indicating that a particular import is ambiguous.
 *
 * @author AL
 */
public class AmbiguousImportException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 699763267768804228L;

    private final Import importStatement;

    private final ClassType version1;

    private final ClassType version2;

    /**
     * Constructor without explanation text.
     *
     * @param importStatement the import found to be ambiguous.
     * @param version1 the first possible type.
     * @param version2 the second possible type.
     */
    public AmbiguousImportException(Import importStatement, ClassType version1,
            ClassType version2) {
        this.importStatement = importStatement;
        this.version1 = version1;
        this.version2 = version2;
    }

    /**
     * Constructor with an explanation text.
     *
     * @param s an explanation.
     * @param importStatement the import found to be ambiguous.
     * @param version1 the first possible type.
     * @param version2 the second possible type.
     */
    public AmbiguousImportException(String s, Import importStatement, ClassType version1,
            ClassType version2) {
        super(s);
        this.importStatement = importStatement;
        this.version1 = version1;
        this.version2 = version2;
    }

    /**
     * Returns the import statement that was found ambiguous.
     */
    public Import getAmbiguousImport() {
        return importStatement;
    }

    /**
     * Returns the possible imported class types.
     */
    public List<ClassType> getChoices() {
        List<ClassType> list = new ArrayList<>(2);
        list.add(version1);
        list.add(version2);
        return list;
    }

}
