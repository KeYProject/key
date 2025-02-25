/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.loader;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import de.uka.ilkd.key.java.KeYJPMapping;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.ast.ResolvedLogicalType;
import de.uka.ilkd.key.java.ast.abstraction.*;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.declaration.modifier.Final;
import de.uka.ilkd.key.java.ast.declaration.modifier.Public;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.util.AssertionFailure;
import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;
import org.key_project.util.collection.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Objects;

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

public class JP2KeYTypeConverter {
    private static final Logger LOGGER = LoggerFactory.getLogger(JP2KeYTypeConverter.class);

    /**
     * builder class for implicit array methods
     *
     * @see #initArrayMethodBuilder()
     */
    private CreateArrayMethodBuilder arrayMethodBuilder;

    private final Services services;

    /**
     * The associated Recoder<->KeY object
     */
    private final KeYJPMapping jp2KeY;
    private final TypeSolver typeSolver;

    private KeYJavaType __objectType;
    private KeYJavaType __cloneableType;
    private KeYJavaType __serializableType;

    public JP2KeYTypeConverter(Services services, TypeSolver typeSolver, KeYJPMapping jp2KeY) {
        this.jp2KeY = jp2KeY;
        this.typeSolver = typeSolver;
        this.services = services;
    }

    public TypeConverter getTypeConverter() {
        return services.getTypeConverter();
    }

    private Namespace<Sort> getSortsNamespace() {
        return services.getNamespaces().sorts();
    }

    private void storeInCache(ResolvedType t, KeYJavaType kjt) {
        jp2KeY.put(t, kjt);
    }

    /**
     * return the corresponding KeY JavaType for a recoder type.
     * <p>
     * Return the cached value if present - otherwise create a new type. Store this in the cache.
     * <p>
     * This method retrieves the recoder nameinfo and queries it for the type for typeName and
     * passes this result to {@link #getKeYJavaType(ResolvedType)}
     *
     * @param typeName name of a type to be converted
     * @return the KJT for the string representation.
     * @author mu
     * @see #getKeYJavaType(ResolvedType)
     */
    public KeYJavaType getKeYJavaType(String typeName) {
        var resolved = typeSolver.solveType(typeName);
        return getKeYJavaType(new ReferenceTypeImpl(resolved));
    }

    public KeYJavaType getKeYJavaType(String typeName, boolean forceInit) {
        var resolved = typeSolver.solveType(typeName);
        return jp2KeY.resolvedTypeToKeY(new ReferenceTypeImpl(resolved), forceInit);
    }


    /**
     * return the corresponding KeY JavaType for a recoder type.
     * <p>
     * Returned the cached value if present - otherwise create a new type.
     *
     * @param type type to be converted, may be null
     * @return a keytype.
     */
    public @NonNull KeYJavaType getKeYJavaType(ResolvedType type) {
        if (type == null) {
            throw new NullPointerException("null cannot be converted into a KJT");
        }

        if (type.isReferenceType() && type.asReferenceType().isJavaLangObject()) {
            return getObjectType();
        }


        {
            // lookup in the cache
            var kjt = jp2KeY.resolvedTypeToKeY(type);
            if (kjt != null) {
                return kjt;
            }
        }

        // create a new KeYJavaType
        if (type.isPrimitive()) {
            addPrimitiveType(type);
        } else if (type.isNull()) {
            addNullType(type);
        } else if (type.isReferenceType()) {
            addReferenceType(type.asReferenceType());
        } else if (type.isArray()) {
            addArrayType(type.asArrayType());
        } else if (type.isVoid()) {
            addVoidType(type);
        } else {
            LOGGER.error("Unexpected type to convert: " + type);
            throw new AssertionFailure("Unexpected type to convert");
        }

        // re-lookup required:
        // usually this equals what was just added in the methods above
        // sometimes however, there is a 'legacy' type in the mapping,
        // which has priority
        return Objects.requireNonNull(jp2KeY.resolvedTypeToKeY(type));
    }

    private void addPrimitiveType(ResolvedType type) {
        var description = type.describe();
        // TODO javaparser why does this use typeConverter? this seems like a loop since it gets
        // initialized by this step
        var primitiveType = PrimitiveType.getPrimitiveType(type.describe());
        var result = getTypeConverter().getKeYJavaType(primitiveType);
        var sort = result.getSort();
        if (sort == null) {
            throw new RuntimeException("Cannot assign " + description + " a primitive sort.");
        }
        storeInCache(type, result);
    }

    private void addNullType(ResolvedType type) {
        var sort = getSortsNamespace().lookup(NullSort.NAME);
        if (sort == null) {
            sort = new NullSort(getObjectType().getSort());
        }
        if (getSortsNamespace().lookup(sort.name()) == null) {
            getSortsNamespace().add(sort);
        }
        storeInCache(type, new KeYJavaType(NullType.JAVA_NULL, sort));
    }

    private void addVoidType(ResolvedType type) {
        storeInCache(type, KeYJavaType.VOID_TYPE);
    }

    private void addArrayType(ResolvedArrayType type) {
        var componentType = type.getComponentType();
        var kjt = getKeYJavaType(componentType);
        // I may not use JavaInfo here because the classes may not yet be cached!
        Type elemType = kjt.getJavaType();
        var arraySort = ArraySort.getArraySort(kjt.getSort(), elemType, getObjectType().getSort(),
                getCloneableType().getSort(), getSerializableType().getSort());
        var result = new KeYJavaType(arraySort);
        if (getSortsNamespace().lookup(arraySort.name()) == null) {
            getSortsNamespace().add(arraySort);
        }

        storeInCache(type, result);

        // delayed creation of virtual array declarations to avoid cycles
        var arrayKJT = Objects.requireNonNull(jp2KeY.resolvedTypeToKeY(type));
        var arrayType = createArrayType(getKeYJavaType(componentType), arrayKJT);
        result.setJavaType(arrayType);
    }

    public KeYJavaType getSerializableType() {
        if (__serializableType == null)
            __serializableType = getKeYJavaType("java.io.Serializable");
        return __serializableType;
    }

    public KeYJavaType getCloneableType() {
        if (__cloneableType == null)
            __cloneableType = getKeYJavaType("java.lang.Cloneable");
        return __cloneableType;
    }

    public KeYJavaType getObjectType() {
        if (__objectType == null) {
            //__objectType = new KeYJavaType(services.getNamespaces().sorts().lookup("java.lang.Object"));
            __objectType = getKeYJavaType("java.lang.Object", true);
        }
        return __objectType;
    }

    private void addReferenceType(ResolvedReferenceType type) {
        var ref = type.asReferenceType().getTypeDeclaration().get();
        if (ref instanceof ResolvedLogicalType) {
            storeInCache(type, ((ResolvedLogicalType) ref).getKeYJavaType());
            return;
        }
        var sort = getSortsNamespace().lookup(new Name(type.describe()));
        if (sort == null) {
            if (ref.isInterface()) {
                sort = createObjectSort(ref, directSuperSorts(ref).add(getObjectType().getSort()));
            } else {
                sort = createObjectSort(ref, directSuperSorts(ref));
            }
        }

        if (getSortsNamespace().lookup(sort.name()) == null) {
            getSortsNamespace().add(sort);
        }

        // Important: javaType is null until being set by visiting the class/interface/enum
        // declaration!
        storeInCache(type, new KeYJavaType(sort));

        // TODO javaparser has no default constructor
        // var cl = ref.getConstructors();
        // if (cl.size() == 1
        // && (cl.get(0) instanceof recoder.abstraction.DefaultConstructor)) {
        // getRecoder2KeYConverter().processDefaultConstructor(
        // (recoder.abstraction.DefaultConstructor) cl.get(0));
        // }
    }


    /**
     * get all direct super sorts of a class type (not transitive)
     *
     * @param classType type to examine, not null
     * @return a freshly created set of sorts
     */
    private ImmutableSet<Sort> directSuperSorts(ResolvedReferenceTypeDeclaration classType) {
        ImmutableSet<Sort> ss = DefaultImmutableSet.nil();
        for (var s : classType.getAncestors()) {
            ss = ss.add(getKeYJavaType(s).getSort());
        }

        if (ss.isEmpty() && !classType.isJavaLangObject()) {
            ss = ss.add(getObjectType().getSort());
        }
        return ss;
    }

    /**
     * create a sort out of a recoder class
     *
     * @param ct     classtype to create for, not null
     * @param supers the set of (direct?) super-sorts
     * @return a freshly created Sort object
     */
    private Sort createObjectSort(ResolvedTypeDeclaration ct, ImmutableSet<Sort> supers) {
        var isAbstract = false;
        if (ct.isClass()) {
            var ast = ct.asClass().toAst();
            if (ast.isPresent()
                    && ast.get() instanceof com.github.javaparser.ast.body.TypeDeclaration<?>) {
                var td = (com.github.javaparser.ast.body.TypeDeclaration<?>) ast.get();
                isAbstract = td.hasModifier(com.github.javaparser.ast.Modifier.Keyword.ABSTRACT);
            }
        }
        final Name name = new Name(ct.getQualifiedName());
        return new SortImpl(name, supers, isAbstract || ct.isInterface());
    }

    @NonNull
    private KeYJavaType getSuperArrayType() {
        var res = jp2KeY.getSuperArrayType();
        if (res == null) {
            res = createSuperArrayType();
            // we want to have exactly one length attribute for this R2K
            // instance (resolving a.length=a.length might get impossible otherwise),
            // therefore we introduce a 'super' array class' which contains the length attribute
            jp2KeY.setSuperArrayType(res);
        }

        return res;
    }

    /**
     * create
     *
     * @param baseType
     * @param arrayType
     * @return the ArrayDeclaration of the given type
     */
    private ArrayDeclaration createArrayType(KeYJavaType baseType, KeYJavaType arrayType) {
        var sat = getSuperArrayType();
        final FieldDeclaration length = ((SuperArrayDeclaration) sat.getJavaType()).length();
        final TypeReference baseTypeRef;

        if (baseType.getJavaType() != null) {
            baseTypeRef = new TypeRef(baseType);
        } else {
            baseTypeRef = new TypeRef(new ProgramElementName(baseType.getSort().name().toString()),
                    0, null, baseType);
        }

        ExtList members = new ExtList();
        members.add(baseTypeRef);
        addImplicitArrayMembers(members, arrayType, baseType,
                (ProgramVariable) length.getFieldSpecifications().get(0).getProgramVariable());

        return new ArrayDeclaration(members, baseTypeRef, sat);
    }

    /**
     * creates a super type for array types.
     * <p>
     * creates the field declaration for the public final integer field <code>length</code>
     */
    @NonNull
    private KeYJavaType createSuperArrayType() {
        KeYJavaType integerType = getKeYJavaType(ResolvedPrimitiveType.INT);

        var superArrayType = new KeYJavaType();
        var specLength =
                new FieldSpecification(new LocationVariable(new ProgramElementName("length"),
                        integerType, superArrayType, false, false, false, true));
        var f = new FieldDeclaration(new Modifier[]{new Public(), new Final()},
                new TypeRef(integerType), new FieldSpecification[]{specLength}, false);
        superArrayType.setJavaType(new SuperArrayDeclaration(f));
        return superArrayType;
    }

    /**
     * Adds several implicit fields and methods to given list of members.
     *
     * @param members  an ExtList with the members of parent
     * @param parent   the KeYJavaType of the array to be enriched by its implicit members
     * @param baseType the KeYJavaType of the parent's element type
     */
    private void addImplicitArrayMembers(ExtList members, KeYJavaType parent, KeYJavaType baseType,
                                         ProgramVariable len) {

        Type base = baseType.getJavaType();
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
     * of the given list
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
     * of the given list
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
        final KeYJavaType integerType = getKeYJavaType(ResolvedPrimitiveType.INT);
        final HeapLDT heapLDT = getTypeConverter().getHeapLDT();
        Sort heapSort = heapLDT == null ? JavaDLTheory.ANY : heapLDT.targetSort();
        int heapCount = (heapLDT == null) ? 1 : (heapLDT.getAllHeaps().size() - 1);
        arrayMethodBuilder =
                new CreateArrayMethodBuilder(integerType, getObjectType(), heapSort, heapCount);
    }

}
