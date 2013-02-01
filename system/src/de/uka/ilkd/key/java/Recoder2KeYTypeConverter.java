// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java;

import java.util.List;

import recoder.ServiceConfiguration;
import recoder.service.NameInfo;
import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Final;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * provide means to convert recoder types to the corresponding KeY type
 * structures.
 * 
 * Results are stored in a HashMap so that subsequent queries will retrieve the
 * same result.
 * 
 * The main method is:
 * 
 * get
 * 
 * @author mattias ulbrich
 * @since jul-07
 */

public class Recoder2KeYTypeConverter {

    /**
     * builder class for implicit array methods
     * 
     * @see #initArrayMethodBuilder()
     */
    private CreateArrayMethodBuilder arrayMethodBuilder;

    /**
     * The type converter provides methods on key types.
     * 
     * set by the constructor
     */
    private final TypeConverter typeConverter;

    /**
     * the namespaces to store new types to.
     * 
     * set by the constructor
     */
    private final NamespaceSet namespaces;

    /**
     * The associated Recoder<->KeY object
     */
    private final Recoder2KeY recoder2key;
    
    private JavaInfo javaInfo;

    public Recoder2KeYTypeConverter(Services services, TypeConverter typeConverter, NamespaceSet namespaces, Recoder2KeY recoder2key) {
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
     * 
     * use the Recoder2KeY object for this
     * 
     * @return not null
     */
    private Recoder2KeYConverter getRecoder2KeYConverter() {
        return recoder2key.getConverter();
    }

    /**
     * return the corresponding KeY JavaType for a recoder type.
     * 
     * Return the cached value if present - otherwise create a new type.
     * Store this in the cache.
     * 
     * This method retrieves the recoder nameinfo and queries it for the
     * type for typeName and passes this result to {@link #getKeYJavaType(Type)}
     * 
     * @param typeName
     *            name of a type to be converted
     * @return the KJT for the string representation.
     * @see #getKeYJavaType(Type)
     * @author mu
     */

    public KeYJavaType getKeYJavaType(String typeName) {
        NameInfo ni = recoder2key.getServiceConfiguration().getNameInfo();
        recoder.abstraction.Type ty = ni.getType(typeName);
        return getKeYJavaType(ty);
    }

    /**
     * return the corresponding KeY JavaType for a recoder type.
     * 
     * Returned the cached value if present - otherwise create a new type.
     * 
     * @param t
     *            type to be converted, may be null
     * @return null iff t == null, otherwise a keytype.
     * 
     */
    public KeYJavaType getKeYJavaType(recoder.abstraction.Type t) {
        
        // change from 2012-02-07: there must be a definite KJT
        if (t == null)
            throw new NullPointerException("null cannot be converted into a KJT");

        // lookup in the cache
        KeYJavaType kjt = lookupInCache(t);
        if (kjt != null) {
            return kjt;
        }

        // create a new KeYJavaType
        Sort s = null;
        if (t instanceof recoder.abstraction.PrimitiveType) {
            s = typeConverter.getPrimitiveSort(PrimitiveType.getPrimitiveType(t
                    .getFullName()));
            if (s == null) {
        	throw new RuntimeException("Cannot assign " + t.getFullName() + " a primitive sort.");
            }
            addKeYJavaType(t, s);
        } else if (t instanceof recoder.abstraction.NullType) {
            s = (Sort) namespaces.sorts().lookup(NullSort.NAME);
            if(s == null) {
        	Sort objectSort = (Sort)namespaces.sorts().lookup(new Name("java.lang.Object"));
        	assert objectSort != null;
        	s = new NullSort(objectSort);
            }
            addKeYJavaType(t, s);
        } else if (t instanceof recoder.abstraction.ParameterizedType) {
            recoder.abstraction.ParameterizedType pt = (recoder.abstraction.ParameterizedType) t;
            return getKeYJavaType(pt.getGenericType());
        } else if (t instanceof recoder.abstraction.ClassType) {
            s = (Sort) namespaces.sorts().lookup(new Name(t.getFullName()));
            if(s == null) {
                recoder.abstraction.ClassType ct = (recoder.abstraction.ClassType) t;
                if (ct.isInterface()) {
                    KeYJavaType objectType = getKeYJavaType("java.lang.Object");
                    if(objectType == null) {
                        throw new RuntimeException(
                        "Missing core class: java.lang.Object must always be present");
                    }
                    s = createObjectSort(ct, directSuperSorts(ct).add(
                            objectType.getSort()));
                } else {
                    s = createObjectSort(ct, directSuperSorts(ct));
                }
            }

            addKeYJavaType(t, s);

            // the unknown classtype has no modelinfo so surround with null check
            if(t.getProgramModelInfo() != null) {
                List<? extends recoder.abstraction.Constructor> cl = t.getProgramModelInfo().getConstructors(
                        (recoder.abstraction.ClassType) t);
                if (cl.size() == 1
                        && (cl.get(0) instanceof recoder.abstraction.DefaultConstructor)) {
                    getRecoder2KeYConverter().processDefaultConstructor(
                            (recoder.abstraction.DefaultConstructor) cl.get(0));
                }
            }
        } else if (t instanceof recoder.abstraction.ArrayType) {
            recoder.abstraction.Type bt = ((recoder.abstraction.ArrayType) t)
            .getBaseType();

            kjt = getKeYJavaType(bt);

            KeYJavaType objectType = getKeYJavaType("java.lang.Object");
            KeYJavaType cloneableType = getKeYJavaType("java.lang.Cloneable");
            KeYJavaType serializableType = getKeYJavaType("java.io.Serializable");
            // I may not use JavaInfo here because the classes may not yet be cached!
            if(objectType == null || cloneableType == null || serializableType == null) {
                throw new RuntimeException(
                "Missing core classes: java.lang.Object, java.lang.Cloneable, java.io.Serializable must always be present");
            }

            // I may not use JavaInfo here because the classes may not yet be cached!
            de.uka.ilkd.key.java.abstraction.Type elemType = kjt.getJavaType();
            s = ArraySort.getArraySort(kjt.getSort(),
        	    		       elemType,
        	    		       objectType.getSort(),
        	    		       cloneableType.getSort(),
        	    		       serializableType.getSort());
            addKeYJavaType(t, s);
        }

        kjt = lookupInCache(t);
        assert kjt != null : "The type may not be null here";
        return kjt;
    }

    private void addKeYJavaType(recoder.abstraction.Type t, Sort s) {
        KeYJavaType result = null;
        if (!(t instanceof recoder.java.declaration.TypeDeclaration)) {
            de.uka.ilkd.key.java.abstraction.Type type;
            if (t instanceof recoder.abstraction.PrimitiveType) {
                type = PrimitiveType.getPrimitiveType(t.getFullName());
                result = typeConverter.getKeYJavaType(type);
                if (result == null) {
                    Debug.out("create new KeYJavaType for primitive type "
                            + t + ". This should not happen");
                    result = new KeYJavaType(type, s);
                }
            } else if (t instanceof recoder.abstraction.NullType) {
                type = NullType.JAVA_NULL;
                result = new KeYJavaType(type, s);
                if(namespaces.sorts().lookup(s.name()) == null) {
                    namespaces.sorts().add(s);
                }
            } else if (t instanceof recoder.abstraction.ArrayType) {
                result = new KeYJavaType(s);
                if(namespaces.sorts().lookup(s.name()) == null) {
                    namespaces.sorts().add(s);
                }                
            } else if (t == recoder2key.getServiceConfiguration().
                    getNameInfo().getUnknownClassType()) {
//              result = makeSimpleKeYType((ClassType)t,s);
//              //TEMP!
//              assert result.getJavaType() != null;
            }
            else {
                Debug.out("recoder2key: unknown type", t);
                Debug.out("Unknown type: " + t.getClass() + " "
                        + t.getFullName());
                Debug.fail();                
            }
        } else {
            if(namespaces.sorts().lookup(s.name()) == null) {
                namespaces.sorts().add(s);
            }            
            result = new KeYJavaType(s);
        }
        storeInCache(t, result);

        // delayed creation of virtual array declarations
        // to avoid cycles
        if (t instanceof recoder.abstraction.ArrayType) {
            result.setJavaType(createArrayType(
                    getKeYJavaType(((recoder.abstraction.ArrayType) t)
                            .getBaseType()), lookupInCache(t)));
        }

        // return was never used, so it is removed and method changed to void (mu)
        // return (KeYJavaType) lookupInCache(t); // usually this equals result,
        // sometimes however, there is a 'legacy' type in the mapping,
        // which has priority
    }


    /**
     * get all direct super sorts of a class type (not transitive)
     * 
     * @param classType
     *            type to examine, not null
     * @return a freshly created set of sorts
     */
    private ImmutableSet<Sort> directSuperSorts(recoder.abstraction.ClassType classType) {

        List<recoder.abstraction.ClassType> supers = classType.getSupertypes();
        ImmutableSet<Sort> ss = DefaultImmutableSet.<Sort>nil();
        for (recoder.abstraction.ClassType aSuper : supers) {
            ss = ss.add(getKeYJavaType(aSuper).getSort());
        }       

        /* ??
		if (classType.getName() == null) {

		}
         */

        if (ss.isEmpty() && !isObject(classType)) {
            ss = ss.add(javaInfo.objectSort());
        }
        return ss;
    }

    /**
     * is the full name of this type "java.lang.Object" or the short name
     * "Object"
     * 
     * @param ct
     *            the type to be checked, not null
     * @return true iff the name is Object
     */
    private boolean isObject(recoder.abstraction.ClassType ct) {
        return "java.lang.Object".equals(ct.getFullName())
        || "Object".equals(ct.getName());
    }

    /**
     * create a sort out of a recoder class
     * 
     * @param ct
     *            classtype to create for, not null
     * @param supers
     *            the set of (direct?) super-sorts
     * @return a freshly created Sort object
     */
    private Sort createObjectSort(recoder.abstraction.ClassType ct, ImmutableSet<Sort> supers) {
        final boolean abstractOrInterface = ct.isAbstract() || ct.isInterface();
        final Name name = new Name(
        	Recoder2KeYConverter.makeAdmissibleName(ct.getFullName()));
        Sort result = new SortImpl(name, supers, abstractOrInterface);
	return result;
    }

    /**
     * create
     * 
     * @param baseType
     * @param arrayType
     * @return the ArrayDeclaration of the given type
     */
    public ArrayDeclaration createArrayType(KeYJavaType baseType,
            KeYJavaType arrayType) {
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
        final FieldDeclaration length = ((SuperArrayDeclaration) recoder2key.rec2key()
                .getSuperArrayType().getJavaType()).length();
        final TypeReference baseTypeRef;

        if (baseType.getJavaType() != null) {
            baseTypeRef = new TypeRef(baseType);
        } else {
            baseTypeRef = new TypeRef(new ProgramElementName(baseType.getSort()
                    .name().toString()), 0, null, baseType);
        }
        members.add(baseTypeRef);
        addImplicitArrayMembers(members, arrayType, baseType,
                (ProgramVariable) length.getFieldSpecifications()
                .get(0).getProgramVariable());

        return new ArrayDeclaration(members, baseTypeRef, recoder2key.rec2key()
                .getSuperArrayType());
    }

    /**
     * creates a super type for array types.
     * 
     * creates the field declaration for the public final integer field
     * <code>length</code>
     */
    private FieldDeclaration createSuperArrayType() {
        KeYJavaType integerType = getKeYJavaType(getServiceConfiguration()
                .getNameInfo().getIntType());

        final KeYJavaType superArrayType = new KeYJavaType();
        recoder2key.rec2key().setSuperArrayType(superArrayType);

        FieldSpecification specLength = new FieldSpecification(
                new LocationVariable(new ProgramElementName("length"),
                        	     integerType, 
                        	     superArrayType, 
                        	     false,
                        	     false));
        FieldDeclaration f = new FieldDeclaration(new Modifier[] {
                new Public(), new Final() }, new TypeRef(integerType),
                new FieldSpecification[] { specLength }, false);
        superArrayType.setJavaType(new SuperArrayDeclaration(f));
        return f;
    }

    /**
     * Adds several implicit fields and methods to given list of members.
     * 
     * @param members
     *            an ExtList with the members of parent
     * @param parent
     *            the KeYJavaType of the array to be enriched by its implicit
     *            members
     * @param baseType
     *            the KeYJavaType of the parent's element type
     */
    private void addImplicitArrayMembers(ExtList members, KeYJavaType parent,
            KeYJavaType baseType, ProgramVariable len) {

        de.uka.ilkd.key.java.abstraction.Type base = baseType.getJavaType();
        int dimension = base instanceof ArrayType ? ((ArrayType) base)
                .getDimension() + 1 : 1;
                TypeRef parentReference = new TypeRef(new ProgramElementName(""
                        + parent.getSort().name()), dimension, null, parent);
                
                // add methods
                // the only situation where base can be null is in case of a
                // reference type
                Expression defaultValue = (base != null ? base.getDefaultValue()
                        : NullLiteral.NULL);

                ImmutableList<Field> fields = filterField(members);

                ProgramVariable length = len;// find("length", fields);

                if (arrayMethodBuilder == null) {
                    initArrayMethodBuilder();
                }	

                final IProgramMethod prepare = arrayMethodBuilder.getPrepareArrayMethod(
										       parentReference, length, defaultValue, fields);

                members.add(arrayMethodBuilder
                        .getArrayInstanceAllocatorMethod(parentReference));
                members.add(prepare);
                members.add(arrayMethodBuilder.getCreateArrayHelperMethod(
                        parentReference, length, fields));
                members.add(arrayMethodBuilder.getCreateArrayMethod(parentReference,
                        prepare, fields));
    }

    /**
     * creates an implicit field of the given name and type
     * 
     * @param name
     *            a String with the name of the implicit field
     * @param typeRef
     *            a TypeReference refering to the type as which the new field
     *            has to be declared
     * @param isStatic
     *            a boolean that forces a field to become static or non static
     * @return the new created FieldDeclaration <br>
     *         </br> </code>private (static) typeRef name</code>
     */
    private FieldDeclaration createImplicitArrayField(String name,
            TypeReference typeRef, boolean isStatic, KeYJavaType prefix) {

        ImplicitFieldSpecification varSpec = new ImplicitFieldSpecification(
                new LocationVariable(new ProgramElementName(Recoder2KeYConverter.makeAdmissibleName(name),
                                     Recoder2KeYConverter.makeAdmissibleName(prefix.getSort().name().toString())),
                                     typeRef.getKeYJavaType(), 
                                     prefix, 
                                     isStatic,
                                     false), 
                typeRef.getKeYJavaType());
        // no recoder dependance
        // insertToMap(recoderVarSpec, varSpec);
        Modifier[] modifiers = new Modifier[isStatic ? 2 : 1];
        modifiers[0] = new Private();
        if (isStatic) {
            modifiers[1] = new Static();
        }
        return new FieldDeclaration(modifiers, typeRef,
                new FieldSpecification[] { varSpec }, false);
    }

    /**
     * extracts all fields out of fielddeclaration
     * 
     * @param field
     *            the FieldDeclaration of which the field specifications have to
     *            be extracted
     * @return a IList<Field> the includes all field specifications found int the
     *         field declaration of the given list
     */
    private ImmutableList<Field> filterField(FieldDeclaration field) {
        ImmutableList<Field> result = ImmutableSLList.<Field>nil();
        ImmutableArray<FieldSpecification> spec = field.getFieldSpecifications();
        for (int i = spec.size() - 1; i >= 0; i--) {
            result = result.prepend(spec.get(i));
        }
        return result;
    }

    /**
     * extracts all field specifications out of the given list. Therefore it
     * descends into field declarations.
     * 
     * @param list
     *            the ExtList with the members of a type declaration
     * @return a IList<Field> the includes all field specifications found int the
     *         field declaration of the given list
     */
    private ImmutableList<Field> filterField(ExtList list) {
        ImmutableList<Field> result = ImmutableSLList.<Field>nil();
        for (Object aList : list) {
            Object pe = aList;
            if (pe instanceof FieldDeclaration) {
                result = result.prepend(filterField((FieldDeclaration) pe));
            }
        }
        return result;
    }

    private void initArrayMethodBuilder() {
        final KeYJavaType integerType = getKeYJavaType(getServiceConfiguration()
                .getNameInfo().getIntType());
        final KeYJavaType objectType = javaInfo.getJavaLangObject();
        Sort heapSort = typeConverter.getHeapLDT() == null
                        ? Sort.ANY
                        : typeConverter.getHeapLDT().targetSort();
        arrayMethodBuilder 
        	= new CreateArrayMethodBuilder(integerType,
        				       objectType,
        				       heapSort);
    }
    
    public TypeConverter getTypeConverter() {
	return typeConverter;
    }

}
