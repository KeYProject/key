/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.ServiceConfiguration;
import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.java.declaration.EnumDeclaration;
import recoder.util.Debug;

/**
 * Handles requests for implicitely defined program model elements. In particular these are
 * {@link recoder.abstraction.NullType},
 * {@link recoder.abstraction.Package},{@link recoder.abstraction.ArrayType},
 * {@link recoder.abstraction.DefaultConstructor}, {@link recoder.abstraction.ImplicitEnumValueOf},
 * {@link recoder.abstraction.ImplicitEnumValues}, and {@link recoder.abstraction.IntersectionType}.
 */
public class DefaultImplicitElementInfo extends DefaultProgramModelInfo
        implements ImplicitElementInfo {

    /**
     * maps type declarations to default constructors
     */
    private final Map<ClassType, DefaultConstructor> type2defaultConstructor =
        new HashMap<>();

    private final Map<EnumDeclaration, List<ImplicitEnumMethod>> type2implicitEnumMethods =
        new HashMap<>();
    private List<ClassType> enumValueOfExceptions = null;

    /**
     * @param config the configuration this services becomes part of.
     */
    public DefaultImplicitElementInfo(ServiceConfiguration config) {
        super(config);
    }

    public DefaultConstructor getDefaultConstructor(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        DefaultConstructor cons = type2defaultConstructor.get(ct);
        if (cons == null) {
            cons = new DefaultConstructor(ct);
            cons.setProgramModelInfo(this);
            type2defaultConstructor.put(ct, cons);
        }
        return cons;
    }

    public List<ImplicitEnumMethod> getImplicitEnumMethods(EnumDeclaration etd) {
        if (etd == null) {
            throw new NullPointerException();
        }
        updateModel();
        List<ImplicitEnumMethod> res = type2implicitEnumMethods.get(etd);
        if (res == null) {
            res = new ArrayList<>(2);
            ImplicitEnumMethod meth = new ImplicitEnumValueOf(etd);
            meth.setProgramModelInfo(this);
            res.add(meth);
            meth = new ImplicitEnumValues(etd);
            meth.setProgramModelInfo(this);
            res.add(meth);
            type2implicitEnumMethods.put(etd, res);
        }
        return res;
    }

    public Type getType(ProgramModelElement pme) {
        if (pme instanceof NullType || pme instanceof ArrayType
                || pme instanceof IntersectionType) {
            return (Type) pme;
        } else if (pme instanceof Package) {
            // valid for Package
            return null;
        } else {
            return getReturnType((Method) pme);
        }
    }

    public Package getPackage(ProgramModelElement pme) {
        if (pme instanceof Package) {
            return (Package) pme;
        }
        if (pme instanceof DefaultConstructor || pme instanceof ImplicitEnumMethod) {
            updateModel();
            return getContainingClassType((Method) pme).getPackage();
        }
        return null;
    }

    public List<? extends ClassType> getTypes(ClassTypeContainer ctc) {
        if (ctc instanceof Package) {
            return serviceConfiguration.getNameInfo().getTypes((Package) ctc);
        }
        if (ctc instanceof DefaultConstructor) {
            return new ArrayList<>(0);
        }
        return null;
    }

    public List<ClassType> getAllTypes(ClassType ct) {
        // valid for NullType
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public ClassTypeContainer getClassTypeContainer(ClassType ct) {
        // valid for NullType
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public List<ClassType> getSupertypes(ClassType ct) {
        if (ct instanceof IntersectionType) {
            return ct.getSupertypes();
        }
        // valid for NullType
        return null;
    }

    public List<ClassType> getAllSupertypes(ClassType ct) {
        // valid for NullType
        if (ct instanceof NullType) {
            List<ClassType> result = new ArrayList<>(1);
            result.add(ct);
            return result;
        }
        if (ct instanceof IntersectionType) {
            return super.getAllSubtypes(ct);
        }
        return null;
    }

    public List<? extends Field> getFields(ClassType ct) {
        // valid for NullType
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public List<Field> getAllFields(ClassType ct) {
        // valid for NullType
        if (ct instanceof IntersectionType) {
            return super.getAllFields(ct);
        }
        return null;
    }

    public List<Method> getMethods(ClassType ct) {
        // valid for NullType
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public List<Method> getAllMethods(ClassType ct) {
        // valid for NullType
        if (ct instanceof IntersectionType) {
            return super.getAllMethods(ct);
        }
        return null;
    }

    public List<Constructor> getConstructors(ClassType ct) {
        // valid for NullType
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public boolean isInterface(ClassType ct) {
        // valid for NullType
        assert ct == getNameInfo().getNullType();
        return false;
    }

    public ClassType getContainingClassType(Member m) {
        if (m instanceof DefaultConstructor || m instanceof ImplicitEnumMethod) {
            return m.getContainingClassType();
        }
        return null;
    }

    public List<Type> getSignature(Method m) {
        if (m instanceof ImplicitEnumValueOf) {
            ArrayList<Type> tal = new ArrayList<>(1);
            tal.add(getServiceConfiguration().getNameInfo().getJavaLangString());
            return tal;
        }
        // valid for Default Constructor and values() in enums.
        return new ArrayList<>(0);
    }

    public List<ClassType> getExceptions(Method m) {
        if (m instanceof ImplicitEnumValueOf) {
            if (enumValueOfExceptions == null) {
                // since list is not visible as mutable to the outside, can cache result here.
                enumValueOfExceptions = new ArrayList<>(2);
                enumValueOfExceptions
                        .add(getNameInfo().getClassType("java.lang.IllegalArgumentException"));
                enumValueOfExceptions
                        .add(getNameInfo().getClassType("java.lang.NullPointerException"));
            }
            return enumValueOfExceptions;
        }
        // valid for Default Constructor and values() in enums.
        return new ArrayList<>(0);
    }

    public Type getReturnType(Method m) {
        if (m instanceof ImplicitEnumValueOf) {
            return m.getContainingClassType();
        } else if (m instanceof ImplicitEnumValues) {
            return getServiceConfiguration().getNameInfo()
                    .createArrayType(m.getContainingClassType());
        }
        // valid for Default Constructor
        return null;
    }
}
