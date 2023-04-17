// This file is part of the RECODER library and protected by the LGPL

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
