/*
 * Created on 01.10.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 *
 */
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
