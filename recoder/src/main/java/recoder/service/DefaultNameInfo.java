/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.AbstractService;
import recoder.ServiceConfiguration;
import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.bytecode.ClassFile;
import recoder.bytecode.ReflectionImport;
import recoder.convenience.Format;
import recoder.io.ClassFileRepository;
import recoder.io.PropertyNames;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.util.Debug;

public class DefaultNameInfo extends AbstractService implements NameInfo, PropertyChangeListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(DefaultNameInfo.class);

    private final static boolean DEBUG = false;
    // search mode codes
    private final static int NO_SEARCH = 0;
    private final static int SEARCH_SOURCE = 1;
    private final static int SEARCH_CLASS = 2;
    private final static int SEARCH_REFLECT = 3;
    /**
     * Maps fully qualified class names to their according types.
     */
    private final Map<String, Type> name2type = new HashMap<>(128);
    /**
     * maps fully qualified variable names to their according variables
     */
    private final Map<String, Field> name2field = new HashMap<>(128);
    /**
     * caches old array types. Needed if types are renamed.
     */
    private final HashMap<ClassType, ArrayList<ArrayType>> removedArrayCache =
        new HashMap<>(128);
    // the predefined types
    private final PrimitiveType booleanType;
    private final PrimitiveType byteType;
    private final PrimitiveType shortType;
    private final PrimitiveType longType;
    private final PrimitiveType intType;
    private final PrimitiveType floatType;
    private final PrimitiveType doubleType;
    private final PrimitiveType charType;
    /**
     * The unknown elements. They are used for error handling and to mark entities as
     * "known-as-unknown" internally.
     */
    private final ProgramModelElement unknownElement = new UnknownProgramModelElement();
    private final ClassType unknownClassType = new UnknownClassType();
    private final Type unknownType = unknownClassType;
    private final Package unknownPackage = new Package("<unknownPackage>", null);
    private final Method unknownMethod = new UnknownMethod();
    private final Constructor unknownConstructor = new UnknownConstructor();
    private final Variable unknownVariable = new UnknownVariable();
    private final Field unknownField = new UnknownField();
    private final AnnotationProperty unknownAnnotationProperty = new UnknownAnnotationProperty();
    /**
     * maps package names to package objects
     */
    private Map<String, Package> name2package = new HashMap<>(64);
    private ClassType nullType;
    private ClassType javaLangObject;
    private ClassType javaLangString;
    private ClassType javaLangClass;
    private ClassType javaLangCloneable;
    private ClassType javaIoSerializable;
    private ClassType javaLangRunnable;
    private ClassType javaLangBoolean;
    private ClassType javaLangByte;
    private ClassType javaLangCharacter;
    private ClassType javaLangShort;
    private ClassType javaLangInteger;
    private ClassType javaLangLong;
    private ClassType javaLangFloat;
    private ClassType javaLangDouble;
    private ClassType javaLangAnnotationAnnotation;
    private ClassType javaLangEnum;
    // the current search mode
    private int[] searchMode;

    /**
     * Creates a new initialized definition table.
     *
     * @param config the configuration this services becomes part of.
     */
    public DefaultNameInfo(ServiceConfiguration config) {
        super(config);
        booleanType = createPrimitiveType("boolean");
        byteType = createPrimitiveType("byte");
        shortType = createPrimitiveType("short");
        longType = createPrimitiveType("long");
        intType = createPrimitiveType("int");
        floatType = createPrimitiveType("float");
        doubleType = createPrimitiveType("double");
        charType = createPrimitiveType("char");
    }

    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        nullType = new NullType(cfg.getImplicitElementInfo());
        createPackage("java.lang");
        cfg.getProjectSettings().addPropertyChangeListener(this);
        updateSearchMode();
    }

    public void propertyChange(PropertyChangeEvent evt) {
        String changedProp = evt.getPropertyName();
        if (changedProp.equals(PropertyNames.CLASS_SEARCH_MODE)) {
            updateSearchMode();
        }
    }

    // parses the class search mode property and creates the internal
    // representation. Ignores everything that does not fit.
    private void updateSearchMode() {
        String prop =
            serviceConfiguration.getProjectSettings().getProperty(PropertyNames.CLASS_SEARCH_MODE);
        if (prop == null) {
            // just in case...
            prop = "";
        }
        searchMode = new int[prop.length()];
        for (int i = 0; i < searchMode.length; i++) {
            switch (prop.charAt(i)) {
            case 's':
            case 'S':
                searchMode[i] = SEARCH_SOURCE;
                break;
            case 'c':
            case 'C':
                searchMode[i] = SEARCH_CLASS;
                break;
            case 'r':
            case 'R':
                searchMode[i] = SEARCH_REFLECT;
                break;
            default:
                searchMode[i] = NO_SEARCH;
            }
        }
    }

    /**
     * creates and initializes a new primitive type with the given name.
     *
     * @param name the name of the primitive type to be registered
     * @return the according type object
     */
    private PrimitiveType createPrimitiveType(String name) {
        PrimitiveType res = new PrimitiveType(name, getImplicitElementInfo());
        name2type.put(res.getName(), res);
        return res;
    }

    final void updateModel() {
        serviceConfiguration.getChangeHistory().updateModel();
    }

    ClassFileRepository getClassFileRepository() {
        return serviceConfiguration.getClassFileRepository();
    }

    SourceFileRepository getSourceFileRepository() {
        return serviceConfiguration.getSourceFileRepository();
    }

    ByteCodeInfo getByteCodeInfo() {
        return serviceConfiguration.getByteCodeInfo();
    }

    SourceInfo getSourceInfo() {
        return serviceConfiguration.getSourceInfo();
    }

    ImplicitElementInfo getImplicitElementInfo() {
        return serviceConfiguration.getImplicitElementInfo();
    }

    public void register(ClassType ct) {
        Debug.assertNonnull(ct);
        String name = ct.getFullName();
        ProgramModelElement ob = name2type.put(name, ct);
        if (ob != null && ob != ct && !(ob instanceof UnknownClassType)) {
            Debug.log(
                "Internal Warning - Multiple registration of " + Format.toString("%N [%i]", ct)
                    + Format.toString(" --- was: %N [%i]", ob));
        }
        // are there old array types which need to be recycled? This happens if
        // ct was actually renamed
        ArrayList al = removedArrayCache.get(ct);
        if (al != null) {
            for (Object o : al) {
                ArrayType at = (ArrayType) o;
                at.makeNames();
                name2type.put(at.getFullName(), at);
            }
        }
    }

    public void register(Field f) {
        Debug.assertNonnull(f);
        name2field.put(f.getFullName(), f);
    }

    public ClassType getJavaLangObject() {
        if (javaLangObject == null) {
            javaLangObject = getClassType("java.lang.Object");
        }
        return javaLangObject;
    }

    public ClassType getJavaLangString() {
        if (javaLangString == null) {
            javaLangString = getClassType("java.lang.String");
        }
        return javaLangString;
    }

    public ClassType getJavaLangBoolean() {
        if (javaLangBoolean == null) {
            javaLangBoolean = getClassType("java.lang.Boolean");
        }
        return javaLangBoolean;
    }

    public ClassType getJavaLangByte() {
        if (javaLangByte == null) {
            javaLangByte = getClassType("java.lang.Byte");
        }
        return javaLangByte;
    }

    public ClassType getJavaLangCharacter() {
        if (javaLangCharacter == null) {
            javaLangCharacter = getClassType("java.lang.Character");
        }
        return javaLangCharacter;
    }

    public ClassType getJavaLangShort() {
        if (javaLangShort == null) {
            javaLangShort = getClassType("java.lang.Short");
        }
        return javaLangShort;
    }

    public ClassType getJavaLangInteger() {
        if (javaLangInteger == null) {
            javaLangInteger = getClassType("java.lang.Integer");
        }
        return javaLangInteger;
    }

    public ClassType getJavaLangLong() {
        if (javaLangLong == null) {
            javaLangLong = getClassType("java.lang.Long");
        }
        return javaLangLong;
    }

    public ClassType getJavaLangFloat() {
        if (javaLangFloat == null) {
            javaLangFloat = getClassType("java.lang.Float");
        }
        return javaLangFloat;
    }

    public ClassType getJavaLangDouble() {
        if (javaLangDouble == null) {
            javaLangDouble = getClassType("java.lang.Double");
        }
        return javaLangDouble;
    }

    public ClassType getJavaLangClass() {
        if (javaLangClass == null) {
            javaLangClass = getClassType("java.lang.Class");
        }
        return javaLangClass;
    }

    public ClassType getJavaLangCloneable() {
        if (javaLangCloneable == null) {
            javaLangCloneable = getClassType("java.lang.Cloneable");
        }
        return javaLangCloneable;
    }

    public ClassType getJavaLangRunnable() {
        if (javaLangRunnable == null) {
            javaLangRunnable = getClassType("java.lang.Runnable");
        }
        return javaLangRunnable;
    }

    public ClassType getJavaIoSerializable() {
        if (javaIoSerializable == null) {
            javaIoSerializable = getClassType("java.io.Serializable");
        }
        return javaIoSerializable;
    }

    public ClassType getJavaLangAnnotationAnnotation() {
        if (javaLangAnnotationAnnotation == null) {
            javaLangAnnotationAnnotation = getClassType("java.lang.annotation.Annotation");
        }
        return javaLangAnnotationAnnotation;
    }

    public ClassType getJavaLangEnum() {
        if (javaLangEnum == null) {
            javaLangEnum = getClassType("java.lang.Enum");
        }
        return javaLangEnum;
    }

    public ClassType getNullType() {
        return nullType;
    }

    public PrimitiveType getShortType() {
        return shortType;
    }

    public PrimitiveType getByteType() {
        return byteType;
    }

    public PrimitiveType getBooleanType() {
        return booleanType;
    }

    public PrimitiveType getIntType() {
        return intType;
    }

    public PrimitiveType getLongType() {
        return longType;
    }

    public PrimitiveType getFloatType() {
        return floatType;
    }

    public PrimitiveType getDoubleType() {
        return doubleType;
    }

    public PrimitiveType getCharType() {
        return charType;
    }

    public boolean isPackage(String name) {
        updateModel();
        return name2package.get(name) != null;
    }

    public Package createPackage(String name) {
        Package result = name2package.get(name);
        if (result == null) {
            result = new Package(name, serviceConfiguration.getImplicitElementInfo());
            name2package.put(result.getName(), result);
            int ldp = name.lastIndexOf('.');
            if (ldp > 0) {
                createPackage(name.substring(0, ldp));
            }
        }
        return result;
    }

    public Package getPackage(String name) {
        Debug.assertNonnull(name);
        updateModel();
        return name2package.get(name);
    }

    public List<Package> getPackages() {
        updateModel();
        int size = name2package.size();
        List<Package> result = new ArrayList<>(size);
        for (Package p : name2package.values()) {
            result.add(p);
        }
        return result;
    }

    public ClassType getClassType(String name) {
        Type result = getType(name);
        if (result instanceof ClassType) {
            return (ClassType) result;
        }
        return null;
    }

    public ArrayType createArrayType(Type basetype) {
        String aname = basetype.getFullName() + "[]";
        ArrayType result = (ArrayType) name2type.get(aname);
        if (result == null) {
            result = new ArrayType(basetype, serviceConfiguration.getImplicitElementInfo());

            name2type.put(result.getFullName(), result);
        }
        return result;
    }

    public ArrayType createArrayType(Type basetype, int dimensions) {
        if (dimensions < 1) {
            throw new IllegalArgumentException("dimensions must be >= 1");
        }
        Type result = basetype;
        while (dimensions-- > 0) {
            result = createArrayType(result);
        }
        return (ArrayType) result;
    }

    public ArrayType getArrayType(Type basetype) {
        Debug.assertNonnull(basetype);
        updateModel();
        String aname = basetype.getFullName() + "[]";
        return (ArrayType) name2type.get(aname);
    }

    public Type getType(String name) {
        Debug.assertNonnull(name);
        updateModel();
        if (DEBUG) {
            Debug.log("Search requested for type " + name);
        }

        Type result = name2type.get(name);
        if (result != null && !name.equals(result.getFullName())) {
            // FIXME
            // System.err.println("Warning: Inconsistend state in name info!");
            // this ain't enough, need to fix this in DefaultSourceInfo somehow...
            name2type.remove(name);
            result = null;
        }
        if (result == unknownType) {
            if (DEBUG) {
                Debug.log(name + " is known to be unknown");
            }
            return null; // report null
        } else if (result == null) {
            if (name.endsWith("]")) {
                result = getType(name.substring(0, name.length() - 2));
                if (result != null) {
                    return createArrayType(result);
                }
            }

            // try to load the required information
            if (result == null && loadClass(name)) {
                result = name2type.get(name);
                if (result == unknownType) {
                    if (DEBUG) {
                        Debug.log(name + " is known to be unknown");
                    }
                    return null;
                }
            }
            // cache positive or negative results
            if (DEBUG && result == null) {
                Debug.log(name + " is set to unknown");
            }
            name2type.put(name, (result != null) ? result : unknownType);
        }
        if (DEBUG && result != null) {
            Debug.log(name + " has been found");
        }
        return result;
    }

    public List<Type> getTypes() {
        updateModel();
        int size = name2type.size();
        List<Type> result = new ArrayList<>(size);
        // size: most types are expected to be known
        for (Type t : name2type.values()) {
            if (t != unknownType) {
                result.add(t);
            }
        }
        return result;
    }

    /*
     * Here is room for improvement: Cache that stuff. That'd require incremental update, though!
     */
    public List<ClassType> getTypes(Package pkg) {
        Debug.assertNonnull(pkg);
        updateModel();
        List<ClassType> result = new ArrayList<>();
        List<Type> tl = getTypes();
        int s = tl.size();
        for (Type t : tl) {
            if (t instanceof ClassType) {
                ClassType ct = (ClassType) t;
                if (ct.getContainer() == pkg) {
                    result.add(ct);
                }
            }
        }
        return result;
    }

    public List<ClassType> getClassTypes() {
        updateModel();
        List<ClassType> result = new ArrayList<>(name2type.size() - 8);
        List<Type> tl = getTypes();
        int s = tl.size();
        for (Type t : tl) {
            if (t instanceof ClassType) {
                result.add((ClassType) t);
            }
        }
        return result;
    }

    public Field getField(String name) {
        Debug.assertNonnull(name);
        updateModel();
        Field result = name2field.get(name);
        if (result != null) {
            return result;
        }
        // we can try to get the type first
        int ldp = name.lastIndexOf('.');
        if (ldp == -1) {
            return null;
        }
        ClassType ct = getClassType(name.substring(0, ldp));
        if (ct == null) {
            return null;
        }
        List<? extends Field> fields = ct.getFields();
        if (fields == null) {
            return null;
        }
        String shortname = name.substring(ldp + 1);
        for (Field field : fields) {
            String fname = field.getName();
            if (/* name == fname || */shortname.equals(fname)) {
                result = field;
                if (result != null) {
                    break;
                }
            }
        }
        return result;
    }

    public List<Field> getFields() {
        updateModel();
        int size = name2field.size();
        List<Field> result = new ArrayList<>(size);
        for (Field f : name2field.values()) {
            result.add(f);
        }
        return result;
    }

    private boolean loadClass(String classname) {
        boolean result = false;
        for (int i = 0; !result && i < searchMode.length; i += 1) {
            switch (searchMode[i]) {
            case SEARCH_SOURCE:
                if (DEBUG) {
                    Debug.log("Searching source code: " + classname);
                }
                result = loadClassFromSourceCode(classname);
                break;
            case SEARCH_CLASS:
                if (DEBUG) {
                    Debug.log("Searching class file: " + classname);
                }
                result = loadClassFromPrecompiledCode(classname);
                break;
            case SEARCH_REFLECT:
                if (DEBUG) {
                    Debug.log("Searching class: " + classname);
                }
                result = loadClassByReflection(classname);
                break;
            default:
                break;
            }
        }
        return result;
    }

    private boolean loadClassFromPrecompiledCode(String classname) {
        boolean result = false;
        ClassFileRepository cfr = getClassFileRepository();
        ClassFile cf = cfr.getClassFile(classname);
        if (cf != null) {
            getByteCodeInfo().register(cf);
            result = true;
        }
        return result;
    }

    private boolean loadClassFromSourceCode(String classname) {
        boolean result = false;
        CompilationUnit cu = null;
        try {
            cu = getSourceFileRepository().getCompilationUnit(classname);
            if (cu == null) {
                // try to load member classes by loading outer classes
                int ldp = classname.lastIndexOf('.');
                if (ldp >= 0) {
                    String shortedname = classname.substring(0, ldp);
                    // not a top-level type, parent type was loaded
                    // and member type has been registered:
                    return !name2package.containsKey(shortedname)
                            && loadClassFromSourceCode(shortedname)
                            && name2type.containsKey(classname);
                }
            }
            if (cu != null) {
                getSourceInfo().register(cu);
                result = true;
            }
        } catch (Exception e) {
            LOGGER.error("Error trying to retrieve source file for type " + classname, e);
        }
        return result;
    }

    private boolean loadClassByReflection(String classname) {
        ClassFile cf = ReflectionImport.getClassFile(classname);
        if (cf != null) {
            getByteCodeInfo().register(cf);
            return true;
        }
        return false;
    }

    public String information() {
        int unknown = 0;
        for (Type t : name2type.values()) {
            if (t == unknownType) {
                unknown += 1;
            }
        }
        return "" + name2package.size() + " packages with " + (name2type.size() - unknown)
            + " types (" + unknown + " were pure speculations) and " + name2field.size()
            + " fields";
    }

    public void unregisterClassType(String fullname) {
        unregisterClassType(fullname, false);
    }

    void unregisterClassType(String fullname, boolean recycleArrayEntries) {
        Debug.assertNonnull(fullname);
        ClassType old = (ClassType) name2type.remove(fullname);
        // deregister array types
        fullname += "[]";
        Type array;
        ArrayList<ArrayType> al = new ArrayList<>();
        while ((array = name2type.remove(fullname)) != null) {
            if (recycleArrayEntries) {
                al.add((ArrayType) array);
            }
            fullname += "[]";
        }
        // Assumes that for any given dimension, all array types with
        // smaller dimensions already exist.
        if (recycleArrayEntries) {
            removedArrayCache.put(old, al);
        }
    }

    public void unregisterField(String fullname) {
        Debug.assertNonnull(fullname);
        name2field.remove(fullname);
    }

    public void unregisterPackages() {
        Map<String, Package> n2p = new HashMap<>(64);
        List<ClassFile> cf = getClassFileRepository().getKnownClassFiles();
        for (int i = cf.size() - 1; i >= 0; i -= 1) {
            ClassTypeContainer ctc = cf.get(i).getContainer();
            if (ctc instanceof Package) {
                n2p.put(ctc.getFullName(), (Package) ctc);
            }
        }
        name2package.clear(); // help gc a bit
        name2package = n2p;
    }

    public ClassType getUnknownClassType() {
        return unknownClassType;
    }

    public ProgramModelElement getUnknownElement() {
        return unknownElement;
    }

    public Package getUnknownPackage() {
        return unknownPackage;
    }

    public Method getUnknownMethod() {
        return unknownMethod;
    }

    public Constructor getUnknownConstructor() {
        return unknownConstructor;
    }

    public Variable getUnknownVariable() {
        return unknownVariable;
    }

    public Field getUnknownField() {
        return unknownField;
    }

    public Type getUnknownType() {
        return unknownType;
    }

    public AnnotationProperty getUnknownAnnotationProperty() {
        return unknownAnnotationProperty;
    }

    /**
     * this method is used if a typerename can be identified by the source info, mainly when an
     * AttachChange of an Identifier follows directly to a DetachChange of an Identifier on the same
     * parent. This leaves ArrayTypes untouched.
     *
     * @param ct
     * @param unregisterFrom
     * @param registerTo
     */
    void handleTypeRename(ClassType ct, String unregisterFrom, String registerTo) {
        boolean register = false;
        boolean unregister = false;
        Object old = name2type.get(registerTo);
        // this might be part of a valid package move, so do not corrupt caches
        if (old == null || old == unknownType) {
            register = true;
        }
        old = name2type.get(unregisterFrom);
        if (old == ct) {
            unregister = true;
        }
        // cannot use unregisterClassType() - original array objects need
        // to stay the same for consistency reasons!
        if (unregister) {
            name2type.remove(unregisterFrom);
        }
        Type removed;
        String newArrayName = registerTo + "[]";
        String arrayRemove = unregisterFrom + "[]";
        while ((removed = name2type.remove(arrayRemove)) != null) {
            name2type.put(newArrayName, removed);
            arrayRemove += "[]";
            newArrayName += "[]";
        }
        if (register) {
            register(ct);
        }

        // original type name is now known to be unknown
        name2type.put(unregisterFrom, unknownClassType); // this prevents reloading of class file
                                                         // from disk

        // fields of this type
        List<? extends Field> fl = ct.getFields();
        for (Field currentField : fl) {
            String fieldremove = unregisterFrom + "." + currentField.getName();
            if (unregister) {
                unregisterField(fieldremove);
            }
            if (register) {
                register(currentField);
            }
        }
    }

    class UnknownProgramModelElement implements ProgramModelElement {
        public String getName() {
            return "<unkownElement>";
        }

        public String getFullName() {
            return getName();
        }

        public ProgramModelInfo getProgramModelInfo() {
            return null;
        }

        public void setProgramModelInfo(@SuppressWarnings("unused") ProgramModelInfo pmi) {
            // ignore/won't happen
        }

        public void validate() {
            // always valid
        }

        public UnknownProgramModelElement deepClone() {
            throw new UnsupportedOperationException("Cannot deep-clone implicit information");
        }

    }

    abstract class UnknownMember extends UnknownProgramModelElement implements Member {
        public ClassType getContainingClassType() {
            return unknownClassType;
        }

        public boolean isFinal() {
            return false;
        }

        public boolean isPrivate() {
            return false;
        }

        public boolean isProtected() {
            return false;
        }

        public boolean isPublic() {
            return true;
        }

        public boolean isStatic() {
            return false;
        }

        public boolean isStrictFp() {
            return false;
        }
    }

    class UnknownClassType extends UnknownMember implements ClassType {
        public String getName() {
            return "<unknownClassType>";
        }

        public ClassTypeContainer getContainer() {
            return null;
        }

        public List<ClassType> getTypes() {
            return new ArrayList<>(0);
        }

        public Package getPackage() {
            return unknownPackage;
        }

        public boolean isInterface() {
            return false;
        }

        public boolean isOrdinaryInterface() {
            return false;
        }

        public boolean isAnnotationType() {
            return true;
        }

        public boolean isEnumType() {
            return false;
        }

        public boolean isOrdinaryClass() {
            return true;
        }

        public boolean isAbstract() {
            return false;
        }

        public List<ClassType> getSupertypes() {
            return new ArrayList<>(0);
        }

        public List<ClassType> getAllSupertypes() {
            List<ClassType> result = new ArrayList<>();
            result.add(this);
            result.add(getJavaLangObject());
            return result;
        }

        public List<? extends Field> getFields() {
            return getJavaLangObject().getFields();
        }

        public List<Field> getAllFields() {
            return getJavaLangObject().getAllFields();
        }

        public List<Method> getMethods() {
            return getJavaLangObject().getMethods();
        }

        public List<Method> getAllMethods() {
            return getJavaLangObject().getAllMethods();
        }

        public List<Constructor> getConstructors() {
            return new ArrayList<>(0);
        }

        public List<ClassType> getAllTypes() {
            return new ArrayList<>(0);
        }

        public List<AnnotationUseSpecification> getAnnotations() {
            return null;
        }

        public List<? extends EnumConstant> getEnumConstants() {
            return null;
        }

        public List<TypeParameterDeclaration> getTypeParameters() {
            return null;
        }
    }

    class UnknownMethod extends UnknownMember implements Method {
        public String getName() {
            return "<unknownMethod>";
        }

        public Package getPackage() {
            return unknownPackage;
        }

        public ClassTypeContainer getContainer() {
            return unknownClassType;
        }

        public List<ClassType> getTypes() {
            return new ArrayList<>(0);
        }

        public boolean isAbstract() {
            return false;
        }

        public boolean isNative() {
            return false;
        }

        public boolean isStrictFp() {
            return false;
        }

        public boolean isSynchronized() {
            return false;
        }

        public List<ClassType> getExceptions() {
            return new ArrayList<>(0);
        }

        public Type getReturnType() {
            return unknownType;
        }

        public List<Type> getSignature() {
            return new ArrayList<>(0);
        }

        public boolean isVarArgMethod() {
            return false;
        }

        public List<AnnotationUseSpecification> getAnnotations() {
            return null;
        }

        public List<? extends TypeParameter> getTypeParameters() {
            return null;
        }
    }

    class UnknownConstructor extends UnknownMethod implements Constructor {
        public String getName() {
            return "<unknownConstructor>";
        }
    }

    class UnknownVariable extends UnknownProgramModelElement implements Variable {
        public String getName() {
            return "<unknownVariable>";
        }

        public boolean isFinal() {
            return false;
        }

        public Type getType() {
            return unknownType;
        }
    }

    class UnknownField extends UnknownMember implements Field {
        public String getName() {
            return "<unknownField>";
        }

        public Type getType() {
            return unknownType;
        }

        public List<AnnotationUseSpecification> getAnnotations() {
            return null;
        }

        public List<? extends TypeArgument> getTypeArguments() {
            return null;
        }
    }

    class UnknownAnnotationProperty extends UnknownMethod implements AnnotationProperty {
        public Object getDefaultValue() {
            return null;
        }
    }
}
