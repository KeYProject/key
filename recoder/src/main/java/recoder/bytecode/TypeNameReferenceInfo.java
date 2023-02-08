/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.bytecode;

public class TypeNameReferenceInfo {
    private final String referencedName;

    public TypeNameReferenceInfo(String trname) {
        this.referencedName = trname;
    }

    public String getReferencedName() {
        return referencedName;
    }

}
