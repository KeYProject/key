/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.*;

import recoder.AbstractService;
import recoder.ServiceConfiguration;
import recoder.TuningParameters;
import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.abstraction.TypeArgument.WildcardMode;
import recoder.bytecode.TypeArgumentInfo;
import recoder.bytecode.TypeParameterInfo;
import recoder.io.PropertyNames;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.util.Debug;

public abstract class DefaultProgramModelInfo extends AbstractService
        implements ProgramModelInfo, TuningParameters {
    final Map<ClassType, ClassTypeCacheEntry> classTypeCache =
        new HashMap<>(256);

    /**
     * @param config the configuration this services becomes part of.
     */
    protected DefaultProgramModelInfo(ServiceConfiguration config) {
        super(config);
    }

    // TODO move to where it belongs ?!
    private static void removeRange(List list, int from) {
        for (int i = list.size() - 1; i >= from; i--) {
            list.remove(i);
        }
    }

    // TODO move to where it belongs ?!
    private static void removeRange(List list, int from, int to) {
        // TODO improve speed!
        if (from > to) {
            to ^= from ^= to ^= from;
        }
        int cnt = to - from;
        while (cnt-- > 0) {
            list.remove(from);
        }
    }

    final ChangeHistory getChangeHistory() {
        return serviceConfiguration.getChangeHistory();
    }

    ErrorHandler getErrorHandler() {
        return serviceConfiguration.getProjectSettings().getErrorHandler();
    }

    NameInfo getNameInfo() {
        return serviceConfiguration.getNameInfo();
    }

    /* protected for KeY */
    protected final void updateModel() {
        getChangeHistory().updateModel();
    }

    /**
     * Internally used to register a subtype link.
     */
    void registerSubtype(ClassType subtype, ClassType supertype) {
        ProgramModelInfo pmi = supertype.getProgramModelInfo();
        if (pmi != this) {
            ((DefaultProgramModelInfo) pmi).registerSubtype(subtype, supertype);
        }
        ClassTypeCacheEntry ctce = classTypeCache.get(supertype);
        if (ctce == null) {
            classTypeCache.put(supertype, ctce = new ClassTypeCacheEntry());
        }
        if (ctce.subtypes == null) {
            ctce.subtypes = new HashSet<>();
        }
        ctce.subtypes.add(subtype);
    }

    /**
     * Internally used to remove a subtype link.
     */
    void removeSubtype(ClassType subtype, ClassType supertype) {
        ProgramModelInfo pmi = supertype.getProgramModelInfo();
        if (pmi != this) {
            ((DefaultProgramModelInfo) pmi).registerSubtype(subtype, supertype);
        }
        ClassTypeCacheEntry ctce = classTypeCache.get(supertype);
        if (ctce != null) {
            if (ctce.subtypes != null) {
                ctce.subtypes.remove(subtype);
            }
        }
    }

    public List<ClassType> getSubtypes(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getSubtypes(ct);
        }
        ClassTypeCacheEntry ctce = classTypeCache.get(ct);
        if (ctce == null) {
            classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        }
        if (ctce.subtypes == null) {
            return new ArrayList<>(0);
        }
        int s = ctce.subtypes.size();
        List<ClassType> result = new ArrayList<>(s);
        for (ClassType subct : ctce.subtypes) {
            result.add(subct);
        }
        return result;
    }

    public List<ClassType> getAllSubtypes(ClassType ct) {
        updateModel();
        List<ClassType> ctl = new SubTypeTopSort().getAllTypes(ct);
        // begin at second entry - the top sort includes the input class
        ctl.remove(0);
        return ctl;
    }

    public List<ClassType> getAllSupertypes(ClassType ct) {
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getAllSupertypes(ct);
        }
        ClassTypeCacheEntry ctce = classTypeCache.get(ct);
        if (ctce == null) {
            classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        }
        if (ctce.allSupertypes == null) {
            computeAllSupertypes(ct, ctce);
        }
        return ctce.allSupertypes;
    }

    private void computeAllSupertypes(ClassType ct, ClassTypeCacheEntry ctce) {
        ctce.allSupertypes = new SuperTypeTopSort().getAllTypes(ct);
    }

    public List<Field> getAllFields(ClassType ct) {
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getAllFields(ct);
        }
        ClassTypeCacheEntry ctce = classTypeCache.get(ct);
        if (ctce == null) {
            classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        }
        if (ctce.allFields == null) {
            computeAllFields(ct, ctce);
        }
        return ctce.allFields;
    }

    private void computeAllFields(ClassType ct, ClassTypeCacheEntry ctce) {
        if (ctce.allSupertypes == null) {
            computeAllSupertypes(ct, ctce);
        }
        List<? extends ClassType> classes = ctce.allSupertypes;
        // if (classes == null) return null;
        int s = classes.size();
        ArrayList<Field> result = new ArrayList<>(s * 4); // simple heuristic
        int result_size = 0;
        for (ClassType c : classes) {
            List<? extends Field> fl = c.getFields();
            if (fl == null) {
                continue;
            }
            int fs = fl.size();
            add_fields: for (Field f : fl) {
                if (isVisibleFor(f, ct)) {
                    String fname = f.getName();
                    for (int k = 0; k < result_size; k++) {
                        Field rf = result.get(k);
                        if (rf.getName() == fname) {
                            continue add_fields;
                        }
                    }
                    result.add(f);
                    result_size++;
                }
            }
        }
        result.trimToSize();
        ctce.allFields = result;
    }

    public List<Method> getAllMethods(ClassType ct) {
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getAllMethods(ct);
        }
        ClassTypeCacheEntry ctce = classTypeCache.get(ct);
        if (ctce == null) {
            classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        }
        if (ctce.allMethods == null) {
            computeAllMethods(ct, ctce);
        }
        return ctce.allMethods;
    }

    private void computeAllMethods(ClassType ct, ClassTypeCacheEntry ctce) {
        if (ctce.allSupertypes == null) {
            computeAllSupertypes(ct, ctce);
        }
        List<? extends ClassType> classes = ctce.allSupertypes;
        int s = classes.size();
        ArrayList<Method> result = new ArrayList<>(s * 8);

        int result_size = 0;
        for (ClassType c : classes) {
            List<? extends Method> ml = c.getMethods();
            if (ml == null) {
                continue;
            }
            int ms = ml.size();
            add_methods: for (Method m : ml) {
                // if (m.isPublic() || m.isProtected() || c == ct ||
                // (!m.isPrivate() && c.getPackage() == ct.getPackage())) {
                if (isVisibleFor(m, ct)) {
                    List<? extends Type> msig = m.getSignature();
                    if (c instanceof ParameterizedType) {
                        ParameterizedType pt = (ParameterizedType) c;
                        List<Type> tmp = new ArrayList<>(msig.size());
                        for (Type t : msig) {
                            if (t instanceof TypeParameter) {
                                int q = 0;
                                for (; q < pt.getGenericType().getTypeParameters().size(); q++) {
                                    if (pt.getGenericType().getTypeParameters().get(q) == t) {
                                        break;
                                    }
                                }
                                if (q < pt.getGenericType().getTypeParameters().size()) {
                                    tmp.add(makeParameterizedType(pt.getTypeArgs().get(q)));
                                } else {
                                    tmp.add(t);
                                }
                            } else {
                                tmp.add(t);
                            }
                        }
                        msig = tmp;
                    }
                    String mname = m.getName();
                    for (int k = 0; k < result_size; k++) {
                        Method rm = result.get(k);
                        if (rm.getName() == mname) {
                            List<? extends Type> rsig = rm.getSignature();
                            if (rsig.equals(msig)) {
                                // skip this method: we already had it
                                continue add_methods;
                            }
                        }
                    }
                    result.add(m);
                    result_size++;
                }
            }
        }
        result.trimToSize();
        ctce.allMethods = result;
    }

    private Type makeParameterizedType(TypeArgument ta) {
        Type bt = null;
        switch (ta.getWildcardMode()) {
        case Super:
        case Any:
            bt = getNameInfo().getJavaLangObject();
            break;
        case None:
        case Extends:
            bt = getBaseType(ta);
            break;
        }
        if (ta.getTypeArguments() == null || ta.getTypeArguments().size() == 0) {
            return bt;
        }
        return new ParameterizedType((ClassType) bt, ta.getTypeArguments());
    }

    public List<ClassType> getAllTypes(ClassType ct) {
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getAllTypes(ct);
        }
        ClassTypeCacheEntry ctce = classTypeCache.get(ct);
        if (ctce == null) {
            classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        }
        if (ctce.allMemberTypes == null) {
            computeAllMemberTypes(ct, ctce);
        }
        return ctce.allMemberTypes;
    }

    private void computeAllMemberTypes(ClassType ct, ClassTypeCacheEntry ctce) {
        if (ctce.allSupertypes == null) {
            computeAllSupertypes(ct, ctce);
        }
        List<? extends ClassType> classes = ctce.allSupertypes;
        int s = classes.size();
        ArrayList<ClassType> result = new ArrayList<>(s);
        int result_size = 0;
        for (ClassType c : classes) {
            List<? extends ClassType> cl = c.getTypes();
            if (cl == null) {
                continue;
            }
            int cs = cl.size();
            add_ClassTypes: for (ClassType hc : cl) {
                // hc == ct may occur as it is admissible for a member class
                // to extend its parent class
                if ((hc != ct) && isVisibleFor(hc, ct)) {
                    String cname = hc.getName();
                    for (int k = 0; k < result_size; k++) {
                        ClassType rc = result.get(k);
                        if (rc.getName() == cname) {
                            continue add_ClassTypes;
                        }
                    }
                    result.add(hc);
                    result_size++;
                }
            }
        }
        result.trimToSize();
        ctce.allMemberTypes = result;
    }

    public PrimitiveType getPromotedType(PrimitiveType a, PrimitiveType b) {
        if (a == b) {
            return a;
        }
        NameInfo ni = getNameInfo();
        if (a == ni.getBooleanType() || b == ni.getBooleanType()) {
            return null;
        }
        if (a == ni.getDoubleType() || b == ni.getDoubleType()) {
            return ni.getDoubleType();
        }
        if (a == ni.getFloatType() || b == ni.getFloatType()) {
            return ni.getFloatType();
        }
        if (a == ni.getLongType() || b == ni.getLongType()) {
            return ni.getLongType();
        }
        return ni.getIntType();
    }

    public boolean isWidening(PrimitiveType from, PrimitiveType to) {
        // we do not handle null's
        if (from == null || to == null) {
            return false;
        }
        // equal types can be coerced
        if (from == to) {
            return true;
        }
        NameInfo ni = getNameInfo();
        // boolean types cannot be coerced into something else
        if (from == ni.getBooleanType() || to == ni.getBooleanType()) {
            return false;
        }
        // everything else can be coerced to a double
        if (to == ni.getDoubleType()) {
            return true;
        }
        // but a double cannot be coerced to anything else
        if (from == ni.getDoubleType()) {
            return false;
        }
        // everything except doubles can be coerced to a float
        if (to == ni.getFloatType()) {
            return true;
        }
        // but a float cannot be coerced to anything but float or double
        if (from == ni.getFloatType()) {
            return false;
        }
        // everything except float or double can be coerced to a long
        if (to == ni.getLongType()) {
            return true;
        }
        // but a long cannot be coerced to anything but float, double or long
        if (from == ni.getLongType()) {
            return false;
        }
        // everything except long, float or double can be coerced to an int
        if (to == ni.getIntType()) {
            return true;
        }
        // but an int cannot be coerced to the remaining byte, char, short
        if (from == ni.getIntType()) {
            return false;
        }
        // between byte, char, short, only one conversion is admissible
        return (from == ni.getByteType() && to == ni.getShortType());
    }

    public boolean isWidening(ClassType from, ClassType to) {
        return isSubtype(from, to);
    }

    public boolean isWidening(ArrayType from, ArrayType to) {
        Type toBase = to.getBaseType();
        if (toBase == getNameInfo().getJavaLangObject()) {
            return true;
        }
        Type fromBase = from.getBaseType();
        if (toBase instanceof PrimitiveType) {
            return toBase.equals(fromBase);
        }
        return isWidening(fromBase, toBase);
    }

    ///// if to == null, returns true (for sake of conveniency)
    public boolean isWidening(Type from, Type to) {
        if (from instanceof ClassType) {
            // arrays are objects,
            // and only non-primitive types can be used as type arguments
            if (to instanceof ClassType) {
                return isWidening((ClassType) from, (ClassType) to);
            } else {
                return (from instanceof NullType)
                        && (to instanceof ArrayType || to instanceof TypeParameter);
            }
        } else if (from instanceof PrimitiveType) {
            if (to instanceof PrimitiveType) {
                return isWidening((PrimitiveType) from, (PrimitiveType) to);
            }
        } else if (from instanceof ArrayType) {
            if (to instanceof ClassType) {
                NameInfo ni = getNameInfo();
                if (to == ni.getJavaLangObject()) {
                    return true;
                }
                if (to == ni.getJavaLangCloneable()) {
                    return true;
                }
                return to == ni.getJavaIoSerializable();
            } else if (to instanceof ArrayType) {
                return isWidening((ArrayType) from, (ArrayType) to);
            }
        }
        return false;
    }

    public boolean isSubtype(ClassType a, ClassType b) {
        boolean result = false;
        if (a instanceof ParameterizedType) {
            // TODO check type arguments (JLS ?15.12.12.2, ?5.1.9)
            a = ((ParameterizedType) a).getGenericType();
        }
        if (b instanceof ParameterizedType) {
            // TODO same here!!
            b = ((ParameterizedType) b).getGenericType();
        }
        if (a instanceof TypeParameter && b instanceof TypeParameter) {
            // TODO check bounds! (see JLS)
            result = true;
        } else if ((a != null) && (b != null)) {
            if ((a == b) || (a == getNameInfo().getNullType())
                    || (b == getNameInfo().getJavaLangObject())) {
                result = true;
            } else {
                // Optimization by non-recursive bfs possible!!!
                List<? extends ClassType> superA = a.getSupertypes();
                if (superA != null) {
                    int s = superA.size();
                    for (int i = 0; (i < s) && !result; i++) {
                        ClassType sa = superA.get(i);
                        if (sa == a) {
                            getErrorHandler().reportError(new CyclicInheritanceException(a));
                        }
                        if (isSubtype(sa, b)) {
                            result = true;
                        }
                    }
                }
            }
        }
        return result;
    }

    public boolean isSupertype(ClassType a, ClassType b) {
        return isSubtype(b, a);
    }

    private final boolean paramMatches(Type ta, Type tb, boolean allowAutoboxing) {
        if (ta == tb) {
            return true;
        }
        while (ta instanceof ArrayType && tb instanceof ArrayType) {
            // if we got arrays of parameterized types, this helps avoiding special cases
            ta = ((ArrayType) ta).getBaseType();
            tb = ((ArrayType) tb).getBaseType();
        }
        if (tb instanceof TypeParameter && ta instanceof ArrayType) {
            TypeParameter tp = (TypeParameter) tb;
            if (tp.getBoundCount() == 0) {
                return true;
            }
            // otherwise, only java.lang.Object is allowed as one and only bound
            if (tp.getBoundCount() > 1) {
                return false;
            }
            return tp.getBoundName(0).equals("java.lang.Object");
        }
        if (tb instanceof TypeParameter && ta instanceof ClassType) {
            TypeParameter tp = (TypeParameter) tb;
            for (int i = 0; i < tp.getBoundCount(); i++) {
                // must be compatible to all bounds!
                ClassType t;
                t = getClassTypeFromTypeParameter(tp, i);
                if (t == null) {
                    // TODO error! (?)
                    System.err.println(tp.getBoundName(i));
                    System.err.println(
                        "cannot resolve type reference in paramMatches/raw type check... TODO");
                    // continue for now
                }
                // I really don't know what the following 2 lines were supposed
                // to do, but they surely trigger a bug, so I took them out for now
                // TODO look at this again!!! - T.Gutzmann
                // if (tp.getBoundTypeArguments(i) != null)
                // t = new ParameterizedType(t, tp.getBoundTypeArguments(i));
                if (!isWidening(ta, t)) {
                    return false;
                }
            }
            return true;
        }
        if (ta != null && !isWidening(ta, tb)) {
            // (un-)boxing conversion possible? (Java 5 only)
            if (allowAutoboxing) {
                if (ta instanceof PrimitiveType
                        && isWidening(getBoxedType((PrimitiveType) ta), tb)) {
                    return true; // ok
                } else {
                    if (!(ta instanceof ClassType)) {
                        return false; // Arrays/Primitive Types can't be unboxed
                    }
                    PrimitiveType unboxedType = getUnboxedType((ClassType) ta);
                    return isWidening(unboxedType, tb); // ok
                }
            } // boxing not successful.
            return false;
        }
        return true;
    }

    private ClassType getClassTypeFromTypeParameter(TypeParameter tp, int i) {
        ClassType t;
        if (tp instanceof TypeParameterDeclaration) {
            // TODO split up in bytecode/sourcecode info
            TypeParameterDeclaration tpd = (TypeParameterDeclaration) tp;
            SourceInfo si = (SourceInfo) this;
            t = (ClassType) si.getType(tpd.getBounds().get(i));
        } else {
            // bytecode
            t = getNameInfo().getClassType(tp.getBoundName(i));
        }
        return t;
    }

    private final boolean internalIsCompatibleSignature(List<Type> a, List<Type> b,
            boolean allowAutoboxing, boolean isVarArgMethod) {
        int s = b.size();
        int n = a.size();
        if (isVarArgMethod) {
            if (s > n + 1) {
                return false; // too few arguments
            }
            // there are arguments that must be matches
            // consider only a's n-(s-1) and b's last arguments, i.e. the var arg part.
            if (s == n) {
                // tb is an array type. However, ta may be the base type of that array, too
                Type ta = a.get(s - 1);
                Type tb = ((ArrayType) b.get(s - 1)).getBaseType();
                if (paramMatches(ta, tb, allowAutoboxing)) {
                    s--; // param ok, don't check again later
                }
                // else: param may match anyway.
            } else {
                Type tb = ((ArrayType) b.get(s - 1)).getBaseType(); // b's variable arity parameter
                for (int i = s - 1; i < n; i++) {
                    Type ta = a.get(i);
                    if (!paramMatches(ta, tb, allowAutoboxing)) {
                        return false; // no match
                    }
                }
                s--; // last parameter has already been checked
            }
        } else if (s != n) {
            return false; // no var args allowed / wrong number or arguments
        }
        for (int i = 0; i < s; i += 1) {
            Type ta = a.get(i);
            Type tb = b.get(i);
            if (!paramMatches(ta, tb, allowAutoboxing)) {
                return false;
            }
        }
        return true;
    }

    public final boolean isCompatibleSignature(List<Type> a, List<Type> b) {
        return internalIsCompatibleSignature(a, b, false, false);
    }

    public final boolean isCompatibleSignature(List<Type> a, List<Type> b, boolean allowAutoboxing,
            boolean bIsVariableArityMethod) {
        return internalIsCompatibleSignature(a, b, allowAutoboxing, bIsVariableArityMethod);
    }

    /**
     * returns the ClassType this primitive type can be boxed to, as specified in Java Language
     * Specification, 3rd edition, 5.1.8
     *
     * @param unboxedType the unboxed, primitive type
     * @return the ClassType this primitive type can be boxed to
     */
    public ClassType getBoxedType(PrimitiveType unboxedType) {
        NameInfo ni = getNameInfo();
        if (unboxedType == ni.getBooleanType()) {
            return ni.getJavaLangBoolean();
        }
        if (unboxedType == ni.getByteType()) {
            return ni.getJavaLangByte();
        }
        if (unboxedType == ni.getCharType()) {
            return ni.getJavaLangCharacter();
        }
        if (unboxedType == ni.getShortType()) {
            return ni.getJavaLangShort();
        }
        if (unboxedType == ni.getIntType()) {
            return ni.getJavaLangInteger();
        }
        if (unboxedType == ni.getLongType()) {
            return ni.getJavaLangLong();
        }
        if (unboxedType == ni.getFloatType()) {
            return ni.getJavaLangFloat();
        }
        if (unboxedType == ni.getDoubleType()) {
            return ni.getJavaLangDouble();
        }
        throw new Error("Unknown primitive type " + unboxedType.getFullName());
    }

    /**
     * return the PrimitiveType this ClassType can be unboxed to, or <code>null</code> if this
     * ClassType cannot be unboxed. Follows the Java Language Specification, 3rd edition, 5.1.8.
     *
     * @param boxedType the ClassType to be unboxed
     * @return The PrimitveType this ClassType can be unboxed to, <code>null</code> if unboxing is
     *         not possible.
     */
    public PrimitiveType getUnboxedType(ClassType boxedType) {
        NameInfo ni = getNameInfo();
        if (boxedType == ni.getJavaLangBoolean()) {
            return ni.getBooleanType();
        }
        if (boxedType == ni.getJavaLangByte()) {
            return ni.getByteType();
        }
        if (boxedType == ni.getJavaLangCharacter()) {
            return ni.getCharType();
        }
        if (boxedType == ni.getJavaLangShort()) {
            return ni.getShortType();
        }
        if (boxedType == ni.getJavaLangInteger()) {
            return ni.getIntType();
        }
        if (boxedType == ni.getJavaLangLong()) {
            return ni.getLongType();
        }
        if (boxedType == ni.getJavaLangFloat()) {
            return ni.getFloatType();
        }
        if (boxedType == ni.getJavaLangDouble()) {
            return ni.getDoubleType();
        }
        return null;
    }

    protected ClassType getOutermostType(ClassType t) {
        ClassTypeContainer c = t;
        ClassTypeContainer cc = t.getContainer();
        while (cc != null && !(cc instanceof Package)) {
            c = cc;
            cc = cc.getContainer();
        }
        return (ClassType) c;
    }

    public boolean isVisibleFor(Member m, ClassType t) {
        if (t instanceof ParameterizedType) {
            t = ((ParameterizedType) t).getGenericType();
        }
        if (m.isPublic()) {
            // public members are always visible
            return true;
        }
        ClassType mt = m.getContainingClassType();
        if (mt == null) {
            // a classless member is not visible
            return false;
        }
        if (mt == t) {
            // all members are visible to their own class
            return true;
        }
        if (m.isPrivate()) {
            // private members are only visible to members that share
            // an outer type
            return getOutermostType(t) == getOutermostType(mt);
        }
        if (mt.getPackage() == t.getPackage()) {
            // non-private members are visible to their own package
            return true;
        }
        if (m.isProtected()) {
            // protected members are visible to subtypes
            return isSubtype(t, mt);
        }
        // all others are not visible
        return false;
    }

    public void filterApplicableMethods(List<Method> list, String name, List<Type> signature,
            ClassType context) {
        boolean allowJava5 = getServiceConfiguration().getProjectSettings().java5Allowed();
        internalFilterApplicableMethods(list, name, signature, context, null, allowJava5);
    }

    // TODO Hack and to be removed (i.e., assign ProgramModelInfo to TypeArgument)
    Type getBaseType(TypeArgument ta) {
        if (ta.getWildcardMode() == WildcardMode.Any) {
            return getNameInfo().getJavaLangObject();
        }
        if (ta.getWildcardMode() == WildcardMode.Super) {
            // this is sufficient for our needs
            return getNameInfo().getJavaLangObject();
        }
        // WildcardMode.None / WildcardMode.Any
        if (ta instanceof TypeArgumentInfo) {
            TypeArgumentInfo tai = (TypeArgumentInfo) ta;
            if (tai.isTypeVariable()) {
                if (tai.getContainingMethodInfo() != null) {
                    if (tai.getContainingMethodInfo().getTypeParameters() != null) {
                        for (TypeParameterInfo tpi : tai.getContainingMethodInfo()
                                .getTypeParameters()) {
                            if (tpi.getName().equals(tai.getTypeName())) {
                                return tpi;
                            }
                        }
                    }
                }
                for (TypeParameterInfo tpi : tai.getContainingClassFile().getTypeParameters()) {
                    if (tpi.getName().equals(tai.getTypeName())) {
                        return tpi;
                    }
                }
                throw new RuntimeException();
            } else {
                return getNameInfo().getClassType(ta.getTypeName());
            }
        }
        if (ta instanceof TypeArgumentDeclaration) {
            SourceInfo si = getServiceConfiguration().getSourceInfo();
            return si.getType(((TypeArgumentDeclaration) ta).getTypeReferenceAt(0));
        }
        return ((ResolvedTypeArgument) ta).type;
    }

    protected List<Type> replaceTypeArgs(List<Type> sig, List<? extends TypeArgument> typeArgs,
            List<? extends TypeParameter> typeParams) {
        List<Type> res = new ArrayList<>(sig.size());
        for (Type type : sig) {
            res.add(replaceTypeArg(type, typeArgs, typeParams).baseType);
        }
        return res;
    }

    ReplaceTypeArgResult replaceTypeArg(Type t, List<? extends TypeArgument> typeArgs,
            List<? extends TypeParameter> typeParams) {
        ReplaceTypeArgResult res = new ReplaceTypeArgResult(t, null);
        if (t instanceof TypeParameter) {
            // find proper type argument
            for (int j = 0; j < typeParams.size(); j++) {
                if (t.equals(typeParams.get(j))) {
                    // found
                    res = new ReplaceTypeArgResult(getBaseType(typeArgs.get(j)),
                        typeArgs.get(j).getWildcardMode());
                    break;
                }
            }
        }
        return res;
    }

    // typeArguments are the type arguments of an explicit generic invocation.
    private void internalFilterApplicableMethods(List<Method> list, String name,
            List<Type> signature, ClassType context, List<? extends TypeArgument> typeArguments,
            boolean allowJava5) {
        Debug.assertNonnull(name, signature, context);
        // the following looks complicated but it pays off
        int s = list.size();
        int i = 0;
        while (i < s) {
            Method m = list.get(i);
            // easy/fast computations first
            if (!name.equals(m.getName()) || !isVisibleFor(m, context)) {
                break;
            }
            List<Type> methodSig = m.getSignature();
            if (m.getTypeParameters() != null) {
                // generic method
                if (typeArguments != null) {
                    if (typeArguments.size() != m.getTypeParameters().size()) {
                        break; // not applicable (?)
                    }
                    methodSig = replaceTypeArguments(methodSig, typeArguments, m);
                } // otherwise, checks against bounds will be done
            }
            if (context instanceof ParameterizedType) {
                ParameterizedType pt = (ParameterizedType) context;
                methodSig = replaceTypeArgs(methodSig, pt.getTypeArgs(),
                    pt.getGenericType().getTypeParameters());
            }
            // context may be a raw type; this is handled in paramMatches!
            if (!internalIsCompatibleSignature(signature, methodSig, allowJava5,
                m.isVarArgMethod() & allowJava5)) {
                break;
            } else {
                i += 1;
            }
        }
        // if no element has been rejected, we are done
        if (i < s) {
            int j = i;
            for (i += 1; i < s; i += 1) {
                Method m = list.get(i);
                // easy/fast computations first
                if (!name.equals(m.getName()) || !isVisibleFor(m, context)) {
                    continue;
                }
                List<Type> methodSig = m.getSignature();
                if (m.getTypeParameters() != null) {
                    // generic method
                    if (typeArguments != null) {
                        if (typeArguments.size() != m.getTypeParameters().size()) {
                            continue; // not applicable (?)
                        }
                        methodSig = replaceTypeArguments(methodSig, typeArguments, m);
                    } // otherwise, checks against bounds will be done
                }
                if (context instanceof ParameterizedType) {
                    ParameterizedType pt = (ParameterizedType) context;
                    methodSig = replaceTypeArgs(methodSig, pt.getTypeArgs(),
                        pt.getGenericType().getTypeParameters());
                }
                // context may be a raw type; this is handled in paramMatches!
                if (internalIsCompatibleSignature(signature, methodSig, allowJava5,
                    m.isVarArgMethod() & allowJava5)) {
                    list.set(j, m);
                    j += 1;
                }
            }
            removeRange(list, j);
        }
    }

    private List<Type> replaceTypeArguments(List<Type> methodSig,
            List<? extends TypeArgument> typeArguments, Method m) {
        List<Type> res = new ArrayList<>(methodSig.size());
        for (Type type : methodSig) {
            res.add(type);
        }
        for (int l = 0; l < m.getTypeParameters().size(); l++) {
            TypeParameter tp = m.getTypeParameters().get(l);
            for (int k = 0; k < methodSig.size(); k++) {
                Type param = methodSig.get(k);
                if (param instanceof ParameterizedType) {
                    // needs special handling
                    // TODO
                    // System.err.println("Not implemented yet: generic method and type arg is
                    // parameterized");
                } else {
                    if (tp.equals(param)) {
                        Type rep = makeParameterizedType(typeArguments.get(l));
                        res.set(k, rep);
                    }
                }
            }
        }
        return res;
    }

    public void filterMostSpecificMethods(List<Method> list) {
        internalFilterMostSpecificMethods(list, false, false);
    }

    public void filterMostSpecificMethodsPhase2(List<Method> list) {
        internalFilterMostSpecificMethods(list, true, false);
    }

    public void filterMostSpecificMethodsPhase3(List<Method> list) {
        internalFilterMostSpecificMethods(list, true, true);
    }

    private void internalFilterMostSpecificMethods(List<Method> list, boolean allowAutoboxing,
            boolean allowVarArgs) {
        int size = list.size();
        if (size <= 1) {
            return;
        }
        // cache signatures (avoid multiple allocations)
        @SuppressWarnings("unchecked")
        List<Type>[] signatures = new List[size];
        signatures[0] = list.get(0).getSignature();
        // size should not be very large - using a naive n? algorithm
        // signatures/methods to be removed are marked as null
        for (int i = 1; i < size; i += 1) {
            List<Type> sig = signatures[i] = list.get(i).getSignature();
            if (sig != null) {
                for (int j = i - 1; j >= 0; j -= 1) {
                    List<Type> sig2 = signatures[j];
                    if (sig2 != null) {
                        if (internalIsCompatibleSignature(sig2, sig, allowAutoboxing,
                            allowVarArgs & list.get(i).isVarArgMethod())) {
                            // need to doublecheck: is compatible vice versa? (can happen only with
                            // autoboxing or if signatures are exactly the same)
                            if (!allowAutoboxing || !internalIsCompatibleSignature(sig, sig2,
                                allowAutoboxing, false)) {
                                signatures[i] = null;
                            }
                        } else if (internalIsCompatibleSignature(sig, sig2, allowAutoboxing,
                            allowVarArgs & list.get(j).isVarArgMethod())) {
                            // the above special case cannot happen here: vice versa-check has
                            // already been implicitly done)
                            signatures[j] = null;
                            // break; removed because if more than 2 compatible signatures are
                            // found, an error might be falsely reported
                        }
                    }
                }
            }
        }
        // do the cleanup work - remove all less specific methods
        int k = 0;
        for (int i = size - 1; i >= 0; i -= 1) {
            if (signatures[i] == null) {
                k += 1;
            } else if (k > 0) {
                removeRange(list, i + 1, i + k + 1);
                k = 0;
            }
        }
        if (k > 0) {
            removeRange(list, 0, k);
        }
    }

    public List<? extends Constructor> getConstructors(ClassType ct, List<Type> signature,
            List<TypeArgumentDeclaration> typeArgs) {
        Debug.assertNonnull(ct, signature);
        if (ct.isInterface()) {
            if (signature.isEmpty()) {
                // Fake: yield java.lang.Object()
                return getNameInfo().getJavaLangObject().getConstructors();
            }
            return new ArrayList<>(0);
        }
        String name = ct.getName();
        name = name.substring(name.lastIndexOf('.') + 1);

        List<Method> meths =
            internalGetMostSpecificMethods(ct, name, signature, ct.getConstructors(), typeArgs, ct);
        List<Constructor> result = new ArrayList<>();
        for (Method meth : meths) {
            result.add((Constructor) meth);
        }
        return result;
    }

    public List<Method> getMethods(ClassType ct, String name, List<Type> signature,
            List<? extends TypeArgument> typeArgs, ClassType context) {
        return internalGetMostSpecificMethods(ct, name, signature, ct.getAllMethods(), typeArgs,
            context);
    }

    /**
     * calls getMethods with context = ct
     */
    public List<Method> getMethods(ClassType ct, String name, List<Type> signature,
            List<? extends TypeArgument> typeArgs) {
        return internalGetMostSpecificMethods(ct, name, signature, ct.getAllMethods(), typeArgs,
            ct);
    }

    private List<Method> internalGetMostSpecificMethods(ClassType ct, String name,
            List<Type> signature, List<? extends Method> meths,
            List<? extends TypeArgument> typeArgs, ClassType context) {
        Debug.assertNonnull(ct, name, signature);
        boolean allowJava5 = Boolean.valueOf(
            getServiceConfiguration().getProjectSettings().getProperty(PropertyNames.JAVA_5));

        List<Method> result;
        if (allowJava5) {
            /* see JLS 3rd edition chapter 15.12.2 */
            result = doThreePhaseFilter(meths, signature, name, context, typeArgs);
        } else {
            // No java 5 - just one pass
            result = new ArrayList<>(meths);
            internalFilterApplicableMethods(result, name, signature, context, null, false);
            filterMostSpecificMethods(result);
        }
        return result;
    }

    public List<Method> doThreePhaseFilter(List<? extends Method> methods, List<Type> signature,
            String name, ClassType context, List<? extends TypeArgument> typeArgs) {
        /* phase 1. see JLS 3rd edition chapter 15.12.2 */
        List<Method> applicableMethods = new ArrayList<>(methods.size() + 1);
        applicableMethods.addAll(methods);
        internalFilterApplicableMethods(applicableMethods, name, signature, context, typeArgs,
            true);
        if (applicableMethods.size() < 2) {
            return applicableMethods;
        }

        // applicableMethods now contains correct content. Work on copy of this list, now
        List<Method> result = new ArrayList<>(applicableMethods.size() + 1);
        result.addAll(applicableMethods);

        // for first pass, we need to filter again, but on already reduced set only
        internalFilterApplicableMethods(result, name, signature, context, typeArgs, false);
        filterMostSpecificMethods(result);
        if (result.size() > 0) {
            return result;
        }

        result.addAll(applicableMethods); // result is empty at this point
        filterMostSpecificMethodsPhase2(result);
        if (result.size() > 0) {
            return result;
        }
        result.addAll(applicableMethods); // once again, result is empty
        filterMostSpecificMethodsPhase3(result);
        return result;
    }

    public void reset() {
        // it would be possible to reuse cache entry objects by
        // iterating over the cache and erasing all cached lists only.
        // however, whole class types might have vanished and their entries
        // have to vanish, too, so there is little choice
        classTypeCache.clear();
    }

    /**
     * Takes an (Array|Class)Type and adds type arguments to it.
     *
     * @return
     * @throws AssertionError if t is neither a Class or Array Type
     * @throws ClassCastException if t is an array type with a primitive type as base type.
     */
    protected Type makeParameterizedArrayType(Type t, List<? extends TypeArgument> typeArgs) {
        assert t instanceof ArrayType || t instanceof ClassType;
        Type result = t;
        int dim = 0;
        while (result instanceof ArrayType) {
            result = ((ArrayType) result).getBaseType();
            dim++;
        }
        result = new ParameterizedType((ClassType) result, typeArgs);
        for (int i = 0; i < dim; i++) {
            result = getNameInfo().createArrayType(result);
        }
        return result;
    }

    public List<Method> getMethods(ClassType ct, String name, List<Type> signature) {
        return getMethods(ct, name, signature, null);
    }

    public List<? extends Constructor> getConstructors(ClassType ct, List<Type> signature) {
        return getConstructors(ct, signature, null);
    }

    static class ResolvedTypeArgument implements TypeArgument {
        final WildcardMode wm;
        final Type type;
        final List<? extends TypeArgument> typeArgs;

        public ResolvedTypeArgument(WildcardMode wm, Type type,
                List<? extends TypeArgument> typeArgs) {
            if (!(type instanceof ArrayType || type instanceof ClassType)) {
                throw new IllegalArgumentException();
            }
            this.wm = wm;
            this.type = type;
            this.typeArgs = typeArgs;
        }

        public WildcardMode getWildcardMode() {
            return wm;
        }

        public String getTypeName() {
            return type.getFullName();
        }

        public List<? extends TypeArgument> getTypeArguments() {
            return typeArgs;
        }

    }

    static class ClassTypeCacheEntry {
        List<ClassType> supertypes; // used in specialized services only

        Set<ClassType> subtypes;

        List<ClassType> allSupertypes;

        List<ClassType> allMemberTypes;

        List<Field> allFields;

        List<Method> allMethods;
    }

    static class SuperTypeTopSort extends ClassTypeTopSort {

        protected final List<ClassType> getAdjacent(ClassType c) {
            return c.getSupertypes();
        }
    }

    static class ReplaceTypeArgResult {
        final Type baseType;
        final WildcardMode wildcardMode;

        ReplaceTypeArgResult(Type t, WildcardMode wm) {
            this.baseType = t;
            this.wildcardMode = wm;
        }
    }

    class SubTypeTopSort extends ClassTypeTopSort {

        protected final List<ClassType> getAdjacent(ClassType c) {
            return getSubtypes(c);
        }
    }
}
