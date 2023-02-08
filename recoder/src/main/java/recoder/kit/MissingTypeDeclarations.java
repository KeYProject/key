/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL

package recoder.kit;

import recoder.abstraction.ClassType;

import java.util.List;


/**
 * Problem report indicating that certain class types have no source representation.
 */
public class MissingTypeDeclarations extends MissingSources {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6106584488830182556L;

    private final List<ClassType> nonTypeDeclarations;

    public MissingTypeDeclarations(List<ClassType> nonTypeDeclarations) {
        this.nonTypeDeclarations = nonTypeDeclarations;
    }

    public List<ClassType> getNonTypeDeclarations() {
        return nonTypeDeclarations;
    }
}
