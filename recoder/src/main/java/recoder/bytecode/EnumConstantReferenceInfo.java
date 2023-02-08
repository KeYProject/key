/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.bytecode;


/**
 * This is a container class for references to enum constants, which may appear in bytecode
 * annotations.
 *
 * @author Tobias Gutzmann
 */
public class EnumConstantReferenceInfo {

    private final String typeName;
    private final String constName;

    public EnumConstantReferenceInfo(String typeName, String constName) {
        this.typeName = typeName;
        this.constName = constName;
    }

    public String getTypeName() {
        return typeName;
    }

    public String getConstName() {
        return constName;
    }

}
