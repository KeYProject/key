/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import java.util.List;

import recoder.abstraction.ClassType;


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
