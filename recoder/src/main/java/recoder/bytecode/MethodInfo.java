/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import java.util.List;

import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.convenience.Naming;

public class MethodInfo extends MemberInfo implements Method {

    protected final String[] paramtypes;

    protected String returntype;

    protected final String[] exceptions;

    protected AnnotationUseInfo[][] paramAnnotations;

    protected List<TypeArgumentInfo>[] paramTypeArgs;

    protected List<TypeParameterInfo> typeParms;

    public MethodInfo(int accessFlags, String returntype, String name, String[] paramtypes,
            String[] exceptions, ClassFile cf) {
        super(accessFlags, name, cf);
        if (returntype != null) {
            this.returntype = returntype.intern();
        }
        this.paramtypes = paramtypes;
        for (int i = 0; i < paramtypes.length; i++) {
            paramtypes[i] = paramtypes[i].intern();
        }
        this.exceptions = exceptions;
        if (exceptions != null) {
            for (int i = 0; i < exceptions.length; i++) {
                exceptions[i] = exceptions[i].intern();
            }
        }
    }

    public final String[] getParameterTypeNames() {
        return paramtypes;
    }

    public final AnnotationUseInfo[] getAnnotationsForParam(int paramNum) {
        if (paramAnnotations == null) {
            return null;
        }
        return paramAnnotations[paramNum];
    }

    public final List<TypeArgumentInfo> getTypeArgumentsForParam(int paramNum) {
        if (paramTypeArgs == null) {
            return null;
        }
        return paramTypeArgs[paramNum];
    }

    public final List<TypeArgumentInfo> getTypeArgumentsForReturnType() {
        if (paramTypeArgs == null) {
            return null;
        }
        return paramTypeArgs[paramTypeArgs.length - 1];
    }

    public final String[] getExceptionsInfo() {
        return exceptions;
    }

    public final String getTypeName() {
        return returntype;
    }

    public Type getReturnType() {
        return service.getReturnType(this);
    }

    public List<Type> getSignature() {
        return service.getSignature(this);
    }

    public List<ClassType> getExceptions() {
        return service.getExceptions(this);
    }

    public ClassTypeContainer getContainer() {
        return getContainingClassType();
    }

    public Package getPackage() {
        return service.getPackage(this);
    }

    public List<? extends ClassType> getTypes() {
        return service.getTypes(this);
    }

    public String getFullName() {
        return Naming.getFullName(this);
        /*
         * ClassType ct = getContainingClassType(); if (ct == null) { throw new
         * RuntimeException("No class found for " + getName()); } return
         * Naming.dot(ct.getFullName(), getName());
         */
    }

    public boolean isVarArgMethod() {
        return (accessFlags & VARARGS) != 0;
    }

    public List<TypeParameterInfo> getTypeParameters() {
        return typeParms;
    }

}
