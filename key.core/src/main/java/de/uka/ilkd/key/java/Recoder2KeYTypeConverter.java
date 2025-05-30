/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.util.List;

import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Final;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;
import org.key_project.util.collection.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Constructor;
import recoder.abstraction.DefaultConstructor;
import recoder.abstraction.ParameterizedType;
import recoder.java.declaration.TypeDeclaration;
import recoder.service.NameInfo;

/**
 * provide means to convert recoder types to the corresponding KeY type structures.
 * <p>
 * Results are stored in a HashMap so that subsequent queries will retrieve the same result.
 * <p>
 * The main method is:
 * <p>
 * get
 *
 * @author mattias ulbrich
 * @since jul-07
 */

public class Recoder2KeYTypeConverter {
    private static final Logger LOGGER = LoggerFactory.getLogger(Recoder2KeYTypeConverter.class);

    /**
     * builder class for implicit array methods
     *
     * @see #initArrayMethodBuilder()
     */
    private CreateArrayMethodBuilder arrayMethodBuilder;

    /**
     * The type converter provides methods on key types.
     * <p>
     * set by the constructor
     */
    private final TypeConverter typeConverter;

    /**
     * the namespaces to store new types to.
     * <p>
     * set by the constructor
     */
    private final NamespaceSet namespaces;

    /**
     * The associated Recoder<->KeY object
     */
    private final Recoder2KeY recoder2key;

    private final JavaInfo javaInfo;

    public Recoder2KeYTypeConverter(Services services, TypeConverter typeConverter,
            NamespaceSet namespaces, Recoder2KeY recoder2key) {
        super();
        this.typeConverter = typeConverter;
        this.namespaces = namespaces;
        this.recoder2key = recoder2key;
        javaInfo = services.getJavaInfo();
    }

    private KeYJavaType lookupInCache(recoder.abstraction.Type t) {
        ModelElement result = recoder2key.rec2key().toKeY(t);
        Debug.assertTrue(result instanceof KeYJavaType || result == null,
            "result must be a KeYJavaType here", result);
        return (KeYJavaType) result;
    }

    private void storeInCache(recoder.abstraction.Type t, KeYJavaType kjt) {
        recoder2key.rec2key().put(t, kjt);
    }


    private ServiceConfiguration getServiceConfiguration() {
        return recoder2key.getServiceConfiguration();
    }

    /**
     * get the corresponding Recoder2KeYConverter object of this type converter.
     * <p>
     * use the Recoder2KeY object for this
     *
     * @return not null
     */
    private Recoder2KeYConverter getRecoder2KeYConverter() {
        return recoder2key.getConverter();
    }

    /**
     * return the corresponding KeY JavaType for a recoder type.
     * <p>
     * Return the cached value if present - otherwise create a new type. Store this in the cache.
     * <p>
     * This method retrieves the recoder nameinfo and queries it for the type for typeName and
     * passes this result to {@link #getKeYJavaType(recoder.abstraction.Type)}}
     *
     * @param typeName name of a type to be converted
     * @return the KJT for the string representation.
     * @author mu
     * @see #getKeYJavaType(recoder.abstraction.Type)
     */

    public KeYJavaType getKeYJavaType(String typeName) {
        NameInfo ni = recoder2key.getServiceConfiguration().getNameInfo();
        recoder.abstraction.Type ty = ni.getType(typeName);
        return getKeYJavaType(ty);
    }

    /**
     * return the corresponding KeY JavaType for a recoder type.
     * <p>
     * Returned the cached value if present - otherwise create a new type.
     *
     * @param t type to be converted, may be null
     * @return null iff t == null, otherwise a keytype.
     */
    public KeYJavaType getKeYJavaType(recoder.abstraction.Type t) {

        // change from 2012-02-07: there must be a definite KJT
        if (t == null) {
            throw new NullPointerException("null cannot be converted into a KJT");
        }

        // lookup in the cache
        KeYJavaType kjt = lookupInCache(t);
        if (kjt != null) {
            return kjt;
        }

        // create a new KeYJavaType
        Sort s = null;
        if (t instanceof recoder.abstraction.PrimitiveType) {
            s = typeConverter.getPrimitiveSort(PrimitiveType.getPrimitiveType(t.getFullName()));
            if (s == null) {
                throw new RuntimeException(
                    "Cannot assign " + t.getFullName() + " a primitive sort.");
            }
            addKeYJavaType(t, s);
        } else if (t instanceof recoder.abstraction.NullType) {
            s = namespaces.sorts().lookup(NullSort.NAME);
            if (s == null) {
                Sort objectSort = namespaces.sorts().lookup(new Name("java.lang.Object"));
                assert objectSort != null;
                s = new NullSort(objectSort);
            }
            addKeYJavaType(t, s);
        } else if (t instanceof ParameterizedType pt) {
            return getKeYJavaType(pt.getGenericType());
        } else if (t instanceof ClassType) {
            s = namespaces.sorts().lookup(new Name(t.getFullName()));
            if (s == null) {
                ClassType ct = (ClassType) t;
                if (ct.isInterface()) {
                    KeYJavaType objectType = getKeYJavaType("java.lang.Object");
                    if (objectType == null) {
                        throw new RuntimeException(
                            "Missing core class: java.lang.Object must always be present");
                    }
                    s = createObjectSort(ct, directSuperSorts(ct).add(objectType.getSort()));
                } else {
                    s = createObjectSort(ct, directSuperSorts(ct));
                }
            }

            addKeYJavaType(t, s);

            // the unknown classtype has no modelinfo so surround with null check
            if (t.getProgramModelInfo() != null) {
                List<? extends Constructor> cl =
                    t.getProgramModelInfo().getConstructors((ClassType) t);
                if (cl.size() == 1
                        && (cl.get(0) instanceof DefaultConstructor)) {
                    getRecoder2KeYConverter().processDefaultConstructor(
                        (DefaultConstructor) cl.get(0));
                }
            }
        } else if (t instanceof recoder.abstraction.ArrayType) {
            recoder.abstraction.Type bt = ((recoder.abstraction.ArrayType) t).getBaseType();

            kjt = getKeYJavaType(bt);

            KeYJavaType objectType = getKeYJavaType("java.lang.Object");
            KeYJavaType cloneableType = getKeYJavaType("java.lang.Cloneable");
            KeYJavaType serializableType = getKeYJavaType("java.io.Serializable");
            // I may not use JavaInfo here because the classes may not yet be cached!
            if (objectType == null || cloneableType == null || serializableType == null) {
                throw new RuntimeException(
                    "Missing core classes: java.lang.Object, java.lang.Cloneable, java.io.Serializable must always be present");
            }

            // I may not use JavaInfo here because the classes may not yet be cached!
            de.uka.ilkd.key.java.abstraction.Type elemType = kjt.getJavaType();
            s = ArraySort.getArraySort(kjt.getSort(), elemType, objectType.getSort(),
                cloneableType.getSort(), serializableType.getSort());
            addKeYJavaType(t, s);
        }

        kjt = lookupInCache(t);
        assert kjt != null : "The type may not be null here";
        return kjt;
    }

    private void addKeYJavaType(recoder.abstraction.Type t, Sort s) {
        KeYJavaType result = null;
        if (!(t instanceof TypeDeclaration)) {
            de.uka.ilkd.key.java.abstraction.Type type;
            if (t instanceof recoder.abstraction.PrimitiveType) {
                type = PrimitiveType.getPrimitiveType(t.getFullName());
                result = typeConverter.getKeYJavaType(type);
                if (result == null) {
                    LOGGER.debug("create new KeYJavaType for primitive type " + t
                        + ". This should not happen");
                    result = new KeYJavaType(type, s);
                }
            } else if (t instanceof recoder.abstraction.NullType) {
                type = NullType.JAVA_NULL;
                result = new KeYJavaType(type, s);
                if (namespaces.sorts().lookup(s.name()) == null) {
                    namespaces.sorts().add(s);
                }
            } else if (t instanceof recoder.abstraction.ArrayType) {
                result = new KeYJavaType(s);
                if (namespaces.sorts().lookup(s.name()) == null) {
                    namespaces.sorts().add(s);
                }
            } else if (t == recoder2key.getServiceConfiguration().getNameInfo()
                    .getUnknownClassType()) {
                // result = makeSimpleKeYType((ClassType)t,s);
                // //TEMP!
                // assert result.getJavaType() != null;
            } else {
                LOGGER.debug("recoder2key: unknown type {}", t);
                LOGGER.debug("Unknown type: " + t.getClass() + " " + t.getFullName());
                Debug.fail();
            }
        } else {
            if (namespaces.sorts().lookup(s.name()) == null) {
                namespaces.sorts().add(s);
            }
            result = new KeYJavaType(s);
        }
        storeInCache(t, result);

        // delayed creation of virtual array declarations
        // to avoid cycles
        if (t instanceof recoder.abstraction.ArrayType) {
            result.setJavaType(
                createArrayType(getKeYJavaType(((recoder.abstraction.ArrayType) t).getBaseType()),
                    lookupInCache(t)));
        }

        // return was never used, so it is removed and method changed to void (mu)
        // return (KeYJavaType) lookupInCache(t); // usually this equals result,
        // sometimes however, there is a 'legacy' type in the mapping,
        // which has priority
    }


    /**
     * get all direct super sorts of a class type (not transitive)
     *
     * @param classType type to examine, not null
     * @return a freshly created set of sorts
     */
    private ImmutableSet<Sort> directSuperSorts(ClassType classType) {

        List<ClassType> supers = classType.getSupertypes();
        ImmutableSet<Sort> ss = DefaultImmutableSet.nil();
        for (ClassType aSuper : supers) {
            ss = ss.add(getKeYJavaType(aSuper).getSort());
        }

        /*
         * ?? if (classType.getName() == null) {
         *
         * }
         */

        if (ss.isEmpty() && !isObject(classType)) {
            ss = ss.add(javaInfo.objectSort());
        }
        return ss;
    }

    /**
     * is the full name of this type "java.lang.Object" or the short name "Object"
     *
     * @param ct the type to be checked, not null
     * @return true iff the name is Object
     */
    private boolean isObject(ClassType ct) {
        return "java.lang.Object".equals(ct.getFullName()) || "Object".equals(ct.getName());
    }

    /**
     * create a sort out of a recoder class
     *
     * @param ct classtype to create for, not null
     * @param supers the set of (direct?) super-sorts
     * @return a freshly created Sort object
     */
    private Sort createObjectSort(ClassType ct, ImmutableSet<Sort> supers) {
        if (ct instanceof recoder.abstraction.ArrayType at) {
            Sort objectSort = javaInfo.objectSort();
            Sort cloneableSort = javaInfo.cloneableSort();
            Sort serializableSort = javaInfo.serializableSort();
            var aSort = getKeYJavaType(at.getBaseType());
            return ArraySort.getArraySort(aSort.getSort(), objectSort, cloneableSort,
                serializableSort);
        } else {
            final boolean abstractOrInterface = ct.isAbstract() || ct.isInterface();
            final Name name = new Name(Recoder2KeYConverter.makeAdmissibleName(ct.getFullName()));
            return new SortImpl(name, supers, abstractOrInterface);
        }
    }

    /**
     * create
     *
     * @param baseType
     * @param arrayType
     * @return the ArrayDeclaration of the given type
     */
    public ArrayDeclaration createArrayType(KeYJavaType baseType, KeYJavaType arrayType) {
        ExtList members = new ExtList();
        if (recoder2key.rec2key().getSuperArrayType() == null) {
            createSuperArrayType(); // we want to have exactly one
            // length attribute for this R2K
            // instance (resolving
            // a.length=a.length might get
            // impossible otherwise),
            // therefore we introduce a 'super
            // array class' which contains the
            // length attribute
        }
        final FieldDeclaration length =
            ((SuperArrayDeclaration) recoder2key.rec2key().getSuperArrayType().getJavaType())
                    .length();
        final TypeReference baseTypeRef;

        if (baseType.getJavaType() != null) {
            baseTypeRef = new TypeRef(baseType);
        } else {
            baseTypeRef = new TypeRef(new ProgramElementName(baseType.getSort().name().toString()),
                0, null, baseType);
        }
        members.add(baseTypeRef);
        addImplicitArrayMembers(members, arrayType, baseType,
            (ProgramVariable) length.getFieldSpecifications().get(0).getProgramVariable());

        return new ArrayDeclaration(members, baseTypeRef,
            recoder2key.rec2key().getSuperArrayType());
    }

    /**
     * creates a super type for array types.
     * <p>
     * creates the field declaration for the public final integer field <code>length</code>
     */
    private FieldDeclaration createSuperArrayType() {
        KeYJavaType integerType =
            getKeYJavaType(getServiceConfiguration().getNameInfo().getIntType());

        final KeYJavaType superArrayType = new KeYJavaType();
        recoder2key.rec2key().setSuperArrayType(superArrayType);

        FieldSpecification specLength =
            new FieldSpecification(new LocationVariable(new ProgramElementName("length"),
                integerType, superArrayType, false, false, false, true));
        FieldDeclaration f = new FieldDeclaration(new Modifier[] { new Public(), new Final() },
            new TypeRef(integerType), new FieldSpecification[] { specLength }, false);
        superArrayType.setJavaType(new SuperArrayDeclaration(f));
        return f;
    }

    /**
     * Adds several implicit fields and methods to given list of members.
     *
     * @param members an ExtList with the members of parent
     * @param parent the KeYJavaType of the array to be enriched by its implicit members
     * @param baseType the KeYJavaType of the parent's element type
     */
    private void addImplicitArrayMembers(ExtList members, KeYJavaType parent, KeYJavaType baseType,
            ProgramVariable len) {

        de.uka.ilkd.key.java.abstraction.Type base = baseType.getJavaType();
        int dimension = base instanceof ArrayType ? ((ArrayType) base).getDimension() + 1 : 1;
        TypeRef parentReference =
            new TypeRef(new ProgramElementName(String.valueOf(parent.getSort().name())),
                dimension, null, parent);

        // add methods
        // the only situation where base can be null is in case of a
        // reference type
        Expression defaultValue = (base != null ? base.getDefaultValue() : NullLiteral.NULL);

        ImmutableList<Field> fields = filterField(members);

        ProgramVariable length = len;// find("length", fields);

        if (arrayMethodBuilder == null) {
            initArrayMethodBuilder();
        }

        final IProgramMethod prepare =
            arrayMethodBuilder.getPrepareArrayMethod(parentReference, length, defaultValue, fields);

        members.add(arrayMethodBuilder.getArrayInstanceAllocatorMethod(parentReference));
        members.add(prepare);
        members.add(arrayMethodBuilder.getCreateArrayHelperMethod(parentReference, length, fields));
        members.add(arrayMethodBuilder.getCreateArrayMethod(parentReference, prepare, fields));
    }

    /**
     * extracts all fields out of fielddeclaration
     *
     * @param field the FieldDeclaration of which the field specifications have to be extracted
     * @return a IList<Field> the includes all field specifications found int the field declaration
     *         of the given list
     */
    private ImmutableList<Field> filterField(FieldDeclaration field) {
        ImmutableList<Field> result = ImmutableSLList.nil();
        ImmutableArray<FieldSpecification> spec = field.getFieldSpecifications();
        for (int i = spec.size() - 1; i >= 0; i--) {
            result = result.prepend(spec.get(i));
        }
        return result;
    }

    /**
     * extracts all field specifications out of the given list. Therefore it descends into field
     * declarations.
     *
     * @param list the ExtList with the members of a type declaration
     * @return a IList<Field> the includes all field specifications found int the field declaration
     *         of the given list
     */
    private ImmutableList<Field> filterField(ExtList list) {
        ImmutableList<Field> result = ImmutableSLList.nil();
        for (Object aList : list) {
            Object pe = aList;
            if (pe instanceof FieldDeclaration) {
                result = result.prepend(filterField((FieldDeclaration) pe));
            }
        }
        return result;
    }

    private void initArrayMethodBuilder() {
        final KeYJavaType integerType =
            getKeYJavaType(getServiceConfiguration().getNameInfo().getIntType());
        final KeYJavaType objectType = javaInfo.getJavaLangObject();
        final HeapLDT heapLDT = typeConverter.getHeapLDT();
        Sort heapSort = heapLDT == null ? JavaDLTheory.ANY : heapLDT.targetSort();
        int heapCount = (heapLDT == null) ? 1 : (heapLDT.getAllHeaps().size() - 1);
        arrayMethodBuilder =
            new CreateArrayMethodBuilder(integerType, objectType, heapSort, heapCount);
    }

    public TypeConverter getTypeConverter() {
        return typeConverter;
    }

}
