/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import java.util.List;

import recoder.ModelException;
import recoder.convenience.Naming;
import recoder.service.ProgramModelInfo;

/**
 * @author Tobias Gutzmann
 */
public abstract class ImplicitEnumMethod implements Method {
    protected ProgramModelInfo service;

    protected ClassType ownerClass;

    protected String name;

    /**
     * TODO param could actually be made EnumTypeDeclaration! Bytecode doesn't use this...
     */
    public ImplicitEnumMethod(ClassType ownerClass) {
        super();
        if (ownerClass == null) {
            throw new NullPointerException();
        }
        this.ownerClass = ownerClass;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Method#isAbstract()
     */
    public boolean isAbstract() {
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Method#isNative()
     */
    public boolean isNative() {
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Method#isSynchronized()
     */
    public boolean isSynchronized() {
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Method#isVarArgMethod()
     */
    public boolean isVarArgMethod() {
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Member#isFinal()
     */
    public boolean isFinal() {
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Member#isStatic()
     */
    public boolean isStatic() {
        return true;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Member#isPrivate()
     */
    public boolean isPrivate() {
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Member#isProtected()
     */
    public boolean isProtected() {
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Member#isPublic()
     */
    public boolean isPublic() {
        return true;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Member#isStrictFp()
     */
    public boolean isStrictFp() {
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Member#getContainingClassType()
     */
    public ClassType getContainingClassType() {
        return ownerClass;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Member#getAnnotations()
     */
    public List<? extends AnnotationUse> getAnnotations() {
        return null;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ProgramModelElement#getFullName()
     */
    public String getFullName() {
        return Naming.getFullName(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ProgramModelElement#getProgramModelInfo()
     */
    public ProgramModelInfo getProgramModelInfo() {
        return service;
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * recoder.abstraction.ProgramModelElement#setProgramModelInfo(recoder.service.ProgramModelInfo)
     */
    public void setProgramModelInfo(ProgramModelInfo pmi) {
        service = pmi;
    }


    /*
     * (non-Javadoc)
     *
     * @see recoder.ModelElement#validate()
     */
    public void validate() throws ModelException {
        // always valid
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ClassTypeContainer#getTypes()
     */
    public List<ClassType> getTypes() {
        return null;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ClassTypeContainer#getPackage()
     */
    public Package getPackage() {
        return service.getPackage(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ClassTypeContainer#getContainer()
     */
    public ClassTypeContainer getContainer() {
        return getContainingClassType();
    }

    public List<ClassType> getExceptions() {
        return service.getExceptions(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Method#getReturnType()
     */
    public Type getReturnType() {
        return service.getReturnType(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Method#getSignature()
     */
    public List<Type> getSignature() {
        return service.getSignature(this);
    }
}
