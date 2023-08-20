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
import recoder.bytecode.*;
import recoder.convenience.Format;
import recoder.util.Debug;


public class DefaultByteCodeInfo extends DefaultProgramModelInfo implements ByteCodeInfo {

    /**
     * Containment relation. This could be made internal part of the ByteCodeInfo hierarchy.
     */
    private final Map<ProgramModelElement, ClassTypeContainer> element2container =
        new HashMap<>(256);
    /**
     * Member and inner type relation. This could be made part of the NameInfo for packages and part
     * of the ClassFile or the ClassFileCacheEntry.
     */
    private final Map<ClassTypeContainer, List<ClassType>> containedTypes =
        new HashMap<>(32);
    /**
     * signature caching
     */
    private final Map<Method, List<Type>> method2signature = new HashMap<>(128);

    /**
     * @param config the configuration this services becomes part of.
     */
    public DefaultByteCodeInfo(ServiceConfiguration config) {
        super(config);
    }

    private ByteCodeElement getByteCodeElement(ProgramModelElement pme) {
        if (pme instanceof ByteCodeElement) {
            return (ByteCodeElement) pme;
        } else {
            return null;
        }
    }

    public final ClassFile getClassFile(ClassType ct) {
        return (ClassFile) getByteCodeElement(ct);
    }

    public final MethodInfo getMethodInfo(Method m) {
        return (MethodInfo) getByteCodeElement(m);
    }

    public final ConstructorInfo getConstructorInfo(Constructor c) {
        return (ConstructorInfo) getByteCodeElement(c);
    }

    public final FieldInfo getFieldInfo(Field f) {
        return (FieldInfo) getByteCodeElement(f);
    }

    public Type getType(ByteCodeElement bce) {
        Type result = null;
        String typeName = bce.getTypeName();
        if (bce instanceof MethodInfo) {
            MethodInfo mi = (MethodInfo) bce;
            List<? extends TypeParameter> tpl = mi.getContainingClassType().getTypeParameters();
            for (TypeParameter tp : tpl) {
                if (typeName.equals(tp.getName())) {
                    result = tp;
                }
            }
        }
        if (result == null) {
            result = getNameInfo().getType(typeName);
        }
        if (bce instanceof MethodInfo) {
            MethodInfo mi = (MethodInfo) bce;
            List<TypeArgumentInfo> typeArgs = mi.getTypeArgumentsForReturnType();
            if (typeArgs != null && typeArgs.size() != 0) {
                if (result instanceof ArrayType) {
                    result = makeParameterizedArrayType(result, typeArgs);
                } else {
                    // can safely cast, result must not be primitive type if it has type arguments
                    result = new ParameterizedType((ClassType) result, typeArgs);
                }
            }
        }
        return result;
    }

    public Type getType(ProgramModelElement pme) {
        Debug.assertNonnull(pme);
        Type result = null;
        if (pme instanceof Type) {
            result = (Type) pme;
        } else {
            ByteCodeElement bci = getByteCodeElement(pme);
            if (bci == null) {
                result = pme.getProgramModelInfo().getType(pme);
            } else {
                result = getType(bci);
            }
        }
        return result;
    }

    public Package getPackage(ProgramModelElement pme) {
        Debug.assertNonnull(pme);
        ProgramModelElement x = element2container.get(pme);
        while ((x != null) && !(x instanceof Package)) {
            x = element2container.get(x);
        }
        return (Package) x;
    }

    public List<? extends ClassType> getTypes(ClassTypeContainer ctc) {
        Debug.assertNonnull(ctc);
        if (ctc instanceof ByteCodeElement) {
            List<ClassType> ctl = containedTypes.get(ctc);
            return (ctl == null) ? new ArrayList<>(0) : ctl;
        } else {
            return ctc.getProgramModelInfo().getTypes(ctc);
        }
    }

    public ClassTypeContainer getClassTypeContainer(ClassType ct) {
        return element2container.get(ct);
    }

    public List<ClassType> getSupertypes(ClassType ct) {
        Debug.assertNonnull(ct);
        // TODO cache / register (?)
        if (ct instanceof TypeParameterInfo) {
            TypeParameterInfo tp = (TypeParameterInfo) ct;
            List<ClassType> res = new ArrayList<>();
            if (tp.getBoundCount() == 0) {
                // see JLS 3rd edition ?4.4
                res.add(getNameInfo().getJavaLangObject());
            } else {
                for (int i = 0; i < tp.getBoundCount(); i++) {
                    res.add(getNameInfo().getClassType(tp.getBoundName(i)));
                }
            }
            return res;
        }
        ClassFile cf = getClassFile(ct);
        if (cf == null) {
            return ct.getProgramModelInfo().getSupertypes(ct);
        }
        ClassFileCacheEntry cfce = (ClassFileCacheEntry) classTypeCache.get(ct);
        Debug.assertNonnull(cfce); // created during registration
        Debug.assertNonnull(cfce.supertypes); // created during registration
        return cfce.supertypes;
    }

    public List<? extends Field> getFields(ClassType ct) {
        Debug.assertNonnull(ct);
        if (ct instanceof ClassFile) {
            return ((ClassFile) ct).getFieldInfos();
            // return ((ClassFileCacheEntry)classTypeCache.get(ct)).fields;
        } else {
            return ct.getProgramModelInfo().getFields(ct);
        }
    }

    public List<Method> getMethods(ClassType ct) {
        Debug.assertNonnull(ct);
        if (ct instanceof ClassFile) {
            return new ArrayList<>(((ClassFile) ct).getMethodInfos());
            // return ((ClassFileCacheEntry)classTypeCache.get(ct)).methods;
        } else {
            return ct.getProgramModelInfo().getMethods(ct);
        }
    }

    public List<? extends Constructor> getConstructors(ClassType ct) {
        Debug.assertNonnull(ct);
        if (ct instanceof ClassFile) {
            return ((ClassFile) ct).getConstructorInfos();
            // return
            // ((ClassFileCacheEntry)classTypeCache.get(ct)).constructors;
        } else {
            return ct.getProgramModelInfo().getConstructors(ct);
        }
    }

    public ClassType getContainingClassType(Member m) {
        return (ClassType) element2container.get(m);
    }

    public List<Type> getSignature(Method m) {
        Debug.assertNonnull(m);
        List<Type> result;
        MethodInfo mi = getMethodInfo(m);
        if (mi == null) {
            result = m.getProgramModelInfo().getSignature(m);
        } else {
            String[] ptypes = mi.getParameterTypeNames();
            int pcount = ptypes.length;
            if (pcount == 0) {
                result = new ArrayList<>(0);
            } else {
                result = method2signature.get(m);
                if (result == null) {
                    NameInfo ni = getNameInfo();
                    List<Type> res = new ArrayList<>(pcount);
                    for (int i = 0; i < pcount; i++) {
                        Type t = null;
                        String basename = ptypes[i];
                        int dim;
                        if ((dim = basename.indexOf('[')) != -1) // for now, dim isn't the real
                                                                 // dimension.
                        {
                            basename = basename.substring(0, dim);
                        }
                        List<? extends TypeParameter> tpl;
                        boolean checkClassTypeParameters = true;
                        // method's type parameters
                        // TODO this is copy&paste... use only one list!
                        tpl = mi.getTypeParameters();
                        if (tpl != null) {
                            for (TypeParameter tp : tpl) {
                                if (basename.equals(tp.getName())) {
                                    t = tp;
                                    if (dim != -1) {
                                        dim = (ptypes[i].length() - dim) / 2;
                                        while (dim != 0) {
                                            t = ni.createArrayType(tp);
                                            dim--;
                                        }
                                    }
                                    checkClassTypeParameters = false;
                                    break;
                                }
                            }
                        }
                        // class's type parameters
                        if (checkClassTypeParameters) {
                            tpl = mi.getContainingClassType().getTypeParameters();
                            for (TypeParameter tp : tpl) {
                                if (basename.equals(tp.getName())) {
                                    t = tp;
                                    if (dim != -1) {
                                        dim = (ptypes[i].length() - dim) / 2;
                                        while (dim != 0) {
                                            t = ni.createArrayType(tp);
                                            dim--;
                                        }
                                    }
                                    break;
                                }
                            }
                        }
                        if (t == null) {
                            t = ni.getType(ptypes[i]);
                        }
                        if (mi.getTypeArgumentsForParam(i) != null) {
                            if (t instanceof ArrayType) {
                                t = makeParameterizedArrayType(t, mi.getTypeArgumentsForParam(i));
                            } else {
                                t = new ParameterizedType((ClassType) t,
                                    mi.getTypeArgumentsForParam(i));
                            }
                        }
                        res.add(t);
                    }
                    result = res;
                    method2signature.put(m, result);
                }
            }
        }
        return result;
    }

    public List<ClassType> getExceptions(Method m) {
        Debug.assertNonnull(m);
        MethodInfo mi = getMethodInfo(m);
        if (mi == null) {
            return m.getProgramModelInfo().getExceptions(m);
        } else {
            String[] etypes = mi.getExceptionsInfo();
            if (etypes == null || etypes.length == 0) {
                return new ArrayList<>(0);
            }
            List<ClassType> res = new ArrayList<>(etypes.length);
            NameInfo ni = getNameInfo();
            for (String etype : etypes) {
                res.add(ni.getClassType(etype));
            }
            return res;
        }
    }

    public Type getReturnType(Method m) {
        return getType(m);
    }

    public void register(ClassFile cf) {
        Debug.assertNonnull(cf);
        ClassFileCacheEntry cfce = (ClassFileCacheEntry) classTypeCache.get(cf);
        if (cfce != null) {
            // already registered
            return;
        }

        if (cf.getName().equals("package-info")) {
            // this is not really a type, but compiled package annotations. Skip this.
            return;
        }

        cfce = new ClassFileCacheEntry();
        classTypeCache.put(cf, cfce);
        String classname = cf.getPhysicalName();
        NameInfo ni = getNameInfo();

        // register this class name and set model info to avoid cycle
        cf.setProgramModelInfo(this);
        ni.register(cf);

        // get outer scope: package, or outer class
        int ldp = classname.lastIndexOf('$');
        ClassTypeContainer ctc;
        if (ldp >= 0) {
            // we are an inner class
            String outerClassName = classname.substring(0, ldp);
            classname = classname.substring(ldp + 1);
            // hint for name info: we expect a class file here?
            ClassType outerClass = ni.getClassType(outerClassName.replace('$', '.'));
            if (outerClass == null) {
                // shit happens - here in the form of _local_ classes;
                // these are translated into mother$1$child form, but
                // there is no class file "mother$1".
                do {
                    ldp = outerClassName.lastIndexOf('$');
                    if (ldp >= 0) {
                        outerClassName = outerClassName.substring(0, ldp);
                        if (outerClassName.length() > 0) {
                            outerClass = ni.getClassType(outerClassName.replace('$', '.'));
                        }
                    }
                } while (ldp >= 0 && outerClass == null);
            }
            if (outerClass instanceof ClassFile) {
                register((ClassFile) outerClass);
            } else {
                Debug.log("Found a non-ClassFile outer class of " + classname + ":"
                    + Format.toString("%c %N", outerClass));
            }

            // set containment
            ctc = outerClass;
        } else {
            // find package, or create a new one, respectively
            ldp = classname.lastIndexOf('.');
            String packageName = "";
            if (ldp != -1) {
                packageName = classname.substring(0, ldp);
            }
            // set containment link
            ctc = ni.createPackage(packageName);
        }

        // register class in container
        element2container.put(cf, ctc);

        if (ctc instanceof ByteCodeElement) {
            List<ClassType> ctl = containedTypes.computeIfAbsent(ctc, k -> new ArrayList<>());
            ctl.add(cf);
        }

        // register fields
        List<? extends Field> fl = cf.getFieldInfos();
        for (Field f : fl) {
            f.setProgramModelInfo(this);
            element2container.put(f, cf);
            ni.register(f);
        }

        // register methods
        List<? extends Method> ml = cf.getMethodInfos();
        for (Method m : ml) {
            m.setProgramModelInfo(this);
            element2container.put(m, cf);
        }

        // register constructors
        List<? extends Constructor> cl = cf.getConstructorInfos();
        for (Constructor c : cl) {
            c.setProgramModelInfo(this);
            element2container.put(c, cf);
        }
        if (cl.isEmpty() && !cf.isInterface() && !cf.isEnumType()
                && Character.isJavaIdentifierStart(cf.getName().charAt(0))) {
            Debug.log("No constructor defined in " + cf.getFullName());
            // serviceConfiguration.getImplicitElementInfo().getDefaultConstructor(cf)
        }

        // register inner classes, set containment links
        String[] innerClasses = cf.getInnerClassNames();
        if (innerClasses != null) {
            String fullName = cf.getFullName();
            for (String cn : innerClasses) {
                if (cn.equals(fullName)) {
                    continue;
                    // inner classes refer to themselves as inner classes
                    // STUPID
                }
                ni.getClassType(cn); // bad, bad side-effect programming ;)
                /*
                 * Remark by T.Gutzmann: The inner class info is ment for the sole purpose of type
                 * resolving: an inner class and a package-level class may have the same name
                 * (although that violates naming conventions). There are rules for resolving this
                 * problem on source code level; the information required are not available in
                 * bytecode any more, except in the inner class info ;-) As of Recoder 0.80,
                 * references to inner classes of other types are filtered out by the bytecode
                 * parser.
                 *
                 ** It is actually possible to receive a non-classfile here! The semantics of inner
                 * class chunks in class files seems to be a bit weird.
                 ** com.sun.java.swing.plaf.windows.WindowsLookAndFeel.LazyFileChooserIcon contains
                 * an inner class link to javax.swing.UIDefaults.LazyValue, even though it is just a
                 ** subtype. Strange.
                 */

            }
        }

        // create supertypes
        String sname = cf.getSuperClassName();
        String[] inames = cf.getInterfaceNames();
        List<ClassType> list = new ArrayList<>(inames.length + 1);
        if (sname != null) {
            ClassType ct = ni.getClassType(sname);
            if (ct == null) {
                getErrorHandler().reportError(new MissingClassFileException(
                    "Unknown byte code supertype " + sname + " in class " + cf.getFullName(),
                    sname));

            } else {
                List<TypeArgumentInfo> tais = cf.getSuperClassTypeArguments();
                if (tais != null && tais.size() > 0) {
                    ct = new ParameterizedType(ct, tais);
                }
                list.add(ct);
            }
        }
        for (int i = 0; i < inames.length; i++) {
            String iname = inames[i];
            ClassType ct = ni.getClassType(iname);
            if (ct == null) {
                getErrorHandler().reportError(new MissingClassFileException(
                    "Unknown byte code supertype " + iname + " in class " + cf.getFullName(),
                    iname));

            } else {
                List<TypeArgumentInfo> tais = cf.getSuperInterfaceTypeArguments(i);
                if (tais != null && tais.size() > 0) {
                    ct = new ParameterizedType(ct, tais);
                }
                list.add(ct);
            }
        }
        if (list.isEmpty()) {
            ClassType jlo = ni.getJavaLangObject();
            if (cf != jlo) {
                list.add(jlo);
            }
        }
        cfce.supertypes = list;
        for (ClassType classType : list) {
            registerSubtype(cf, classType);
        }
    }

    public Type getAnnotationType(AnnotationUseInfo au) {
        return getNameInfo().getType(au.getFullReferencedName());
    }

    /*
     * We reuse the class type cache for the class file cache entries. We can do that as we create
     * cache entries during registration of class files and registration comes before any query.
     * There is a cache entry for a class file if and only if it has been registered. Therefore, the
     * class file cache may not be reset, which would happen after a call to reset(). However, the
     * byte code info should never have to be resetted as long as we do not change byte code.
     */
    static class ClassFileCacheEntry extends ClassTypeCacheEntry {
        // could be extended by containment links?
    }

}
