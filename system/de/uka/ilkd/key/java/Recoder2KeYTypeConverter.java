// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//Universitaet Koblenz-Landau, Germany
//Chalmers University of Technology, Sweden

//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.



package de.uka.ilkd.key.java;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import recoder.ServiceConfiguration;
import recoder.abstraction.*;
import recoder.abstraction.ClassType;
import recoder.abstraction.Constructor;
import recoder.abstraction.DefaultConstructor;
import recoder.abstraction.Type;
import recoder.bytecode.ClassFile;
import recoder.service.NameInfo;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.NullType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.*;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.recoderext.ClassFileDeclarationBuilder;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.parser.KeYParser;
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
     * builder class for implicit transient array methods
     * 
     * @see #initArrayMethodBuilder()
     */
    private CreateTransientArrayMethodBuilder transientArrayMethodBuilder;

    /**
     * The type converter provides methods on key types.
     * 
     * set by the constructor
     */
    private TypeConverter typeConverter;

    /**
     * the namespaces to store new types to.
     * 
     * set by the constructor
     */
    private NamespaceSet namespaces;

    /**
     * The associated Recoder<->KeY object
     */
    private Recoder2KeY recoder2key;

    public Recoder2KeYTypeConverter(TypeConverter typeConverter, NamespaceSet namespaces, Recoder2KeY recoder2key) {
        super();
        this.typeConverter = typeConverter;
        this.namespaces = namespaces;
        this.recoder2key = recoder2key;
    }

    private KeYJavaType lookupInCache(Type t) {
        ModelElement result = recoder2key.rec2key().toKeY(t);
        Debug.assertTrue(result instanceof KeYJavaType || result == null,
                "result must be a KeYJavaType here", result);
        return (KeYJavaType) result;
    }

    private void storeInCache(Type t, KeYJavaType kjt) {
        recoder2key.rec2key().put(t, kjt);
    }

    private JavaInfo getJavaInfo() {
        return typeConverter != null ? typeConverter.getServices()
                .getJavaInfo() : null;
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
        Type ty = ni.getType(typeName);
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
        if (t == null) {
            return null; // this can originate from 'void'
        }

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
        	// BEGIN Workaround for testcases        	
        	// if someone (including me) has some time and motivation we should restructure the test
        	// cases to work fine with the standard initialisation procedure.
        	
        	// ugly  !!! To execute tests in a reasonable speed we allow
        	// creation of tests here when this method has been invoked 
        	// implicitly by junit.textui.TestRunner
        	// This keeps the workaround local to here without introducing other
        	// dependencies like testing for static variables
        	boolean throwError = true;

        	Throwable stack = new Throwable(); 
        	stack.fillInStackTrace();
        	StackTraceElement[] elements = stack.getStackTrace(); 
        	for (int i = 0; i<elements.length;i++) {
        	    if (elements[i] != null && elements[i].getClassName().equals("junit.textui.TestRunner")) {
        		s = new PrimitiveSort(new Name(t.getFullName()));
        		throwError = false; 
        		break;
        	    }
        	}
        	// END Workaround
        	
        	if (throwError) {
        	    throw new RuntimeException("Cannot assign " + t.getFullName() + " a primitive sort.");
        	}
            }
            addKeYJavaType(t, s);
        } else if (t instanceof recoder.abstraction.NullType) {
            s = Sort.NULL;
            addKeYJavaType(t, s);
        } else if (t instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) t;
            return getKeYJavaType(pt.getGenericType());
        } else if (t instanceof ClassType) {
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
                List<? extends Constructor> cl = t.getProgramModelInfo().getConstructors(
                        (recoder.abstraction.ClassType) t);
                if (cl.size() == 1
                        && (cl.get(0) instanceof recoder.abstraction.DefaultConstructor)) {
                    getRecoder2KeYConverter().processDefaultConstructor(
                            (DefaultConstructor) cl.get(0));
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
            s = ArraySortImpl.getArraySort(kjt.getSort(), 
                    objectType.getSort(),
                    cloneableType.getSort(),
                    serializableType.getSort());
            addKeYJavaType(t, s);
        }

        kjt = lookupInCache(t);
        assert kjt != null : "The type may not be null here";
        return kjt;
    }

    private void addKeYJavaType(Type t, Sort s) {
        KeYJavaType result = null;
        if (!(t instanceof recoder.java.declaration.TypeDeclaration)) {
            de.uka.ilkd.key.java.abstraction.Type type = null;
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
                if (namespaces.sorts().lookup(s.name()) == null) {
                    setUpSort(s);
                }
                result = new KeYJavaType(type, s);
            } else if (t instanceof recoder.abstraction.ArrayType) {
                setUpSort(s);
                result = new KeYJavaType(s);
            } else if (t == recoder2key.getServiceConfiguration().
                    getNameInfo().getUnknownClassType()) {
//              setUpSort(s);
//              result = makeSimpleKeYType((ClassType)t,s);
//              //TEMP!
//              assert result.getJavaType() != null;
            }
            else {
                Debug.out("recoder2key: unknown type", t);
                Debug.out("Unknown type: " + t.getClass() + " "
                        + t.getFullName());
                Debug.fail();
                result = new KeYJavaType();
            }
        } else {
            setUpSort(s);
            result = new KeYJavaType(s);
        }
        storeInCache(t, result);

        // delayed creation of virtual array declarations
        // to avoid cycles
        if (t instanceof recoder.abstraction.ArrayType) {
            result.setJavaType(createArrayType(
                    getKeYJavaType(((recoder.abstraction.ArrayType) t)
                            .getBaseType()), (KeYJavaType) lookupInCache(t)));
        }

        // return was never used, so it is removed and method changed to void (mu)
        // return (KeYJavaType) lookupInCache(t); // usually this equals result,
        // sometimes however, there is a 'legacy' type in the mapping,
        // which has priority
    }

    /**
     * Insert sorts into the namespace, add symbols that may have been defined
     * by a sort to the function namespace (e.g. functions for collection sorts)
     */
    protected void setUpSort(Sort s) {
	namespaces.sorts().add(s);
        KeYParser.addSortAdditionals(s, 
        	namespaces.functions(), namespaces.sorts());
    }

    /**
     * get all direct super sorts of a class type (not transitive)
     * 
     * @param classType
     *            type to examine, not null
     * @return a freshly created set of sorts
     */
    private SetOfSort directSuperSorts(ClassType classType) {

        List<ClassType> supers = classType.getSupertypes();
        SetOfSort ss = SetAsListOfSort.EMPTY_SET;
        for (int i = 0; i < supers.size(); i++) {
            ss = ss.add(getKeYJavaType(supers.get(i)).getSort());
        }       

        /* ??
		if (classType.getName() == null) {

		}
         */

        if (ss.isEmpty() && !isObject(classType)) {
            ss = ss.add(getJavaInfo().getJavaLangObjectAsSort());
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
    private boolean isObject(ClassType ct) {
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
    private Sort createObjectSort(ClassType ct, SetOfSort supers) {
        final boolean abstractOrInterface = ct.isAbstract() || ct.isInterface();
        return new ClassInstanceSortImpl(new Name(Recoder2KeYConverter.makeAdmissibleName(ct.getFullName())), 
                supers,	abstractOrInterface);
    }

    private KeYJavaType makeSimpleKeYType(ClassType ct, Sort s) {
        ProgramElementName name = new ProgramElementName(Recoder2KeYConverter.makeAdmissibleName(ct.getName()));
        ProgramElementName fullname = new ProgramElementName(Recoder2KeYConverter.makeAdmissibleName(ct.getFullName()));
        MemberDeclaration[] members = new MemberDeclaration[0];
        Modifier[] modifiers = new Modifier[0];
        Extends ext = null;
        Implements impl = null;
        boolean parentIsInterface = false;

        TypeDeclaration td = new ClassDeclaration(modifiers, name, ext, fullname, impl,
                members, parentIsInterface , true);
        KeYJavaType kjt = new KeYJavaType(s);
        kjt.setJavaType(td);
        return kjt;
    }

    /**
     * retrieve information from a bytecode class file and store it into the
     * type repository.
     * 
     * @param cf
     *            class file to model
     *            
     * @deprecated now supported in {@link ClassFileDeclarationBuilder}
     */
    private void createTypeDeclaration(ClassFile cf) {

        KeYJavaType classType = getKeYJavaType(cf);

        Modifier[] modifiers = getModifiers(cf);
        ProgramElementName name = new ProgramElementName(Recoder2KeYConverter.makeAdmissibleName(cf.getName()));
        ProgramElementName fullname = new ProgramElementName(Recoder2KeYConverter.makeAdmissibleName(cf.getFullName()));

        List<ClassType> supertype = cf.getSupertypes();

        TypeReference[] implementsTypes = null;
        TypeReference extendType = null;

        // fetch all interfaces.
        LinkedList implementsList = new LinkedList();
        if (supertype != null) {
            for (int i = 0; i < supertype.size(); i++) {
                recoder.abstraction.ClassType ct = supertype.get(i);
                final KeYJavaType kjt = getKeYJavaType(ct);
                final TypeReference tr = new TypeRef(new ProgramElementName(ct
                        .getFullName()), 0, null, kjt);
                if (ct.isInterface()) {
                    implementsList.add(tr);
                } else {
                    Debug.assertTrue(extendType == null);
                    extendType = tr;
                }
            }
            implementsTypes = (TypeReference[]) implementsList
            .toArray(new TypeReference[implementsList.size()]);
        }

        final Extends ext = (extendType == null ? null
                : new Extends(extendType));

        final Implements impl = implementsTypes == null ? null
                : new Implements(implementsTypes);

        final boolean parentIsInterface = cf.getContainingClassType() != null ? cf
                .getContainingClassType().isInterface()
                : false;

                // for the moment no members

                MemberDeclaration[] members = new MemberDeclaration[0];

                TypeDeclaration td;
                if (cf.isInterface()) {
                    td = new InterfaceDeclaration(modifiers, name, fullname, ext,
                            members, true);
                } else {
                    td = new ClassDeclaration(modifiers, name, ext, fullname, impl,
                            members, parentIsInterface, true);
                }
                classType.setJavaType(td);

                // now void
                // return td;
    }

    /**
     * retrieve the modiefiers of <tt>cf</tt>
     * 
     * @param cf
     *            the ByteCodeElement whose modifiers are determined
     * @return cf's modifiers
     */
    private Modifier[] getModifiers(recoder.bytecode.ByteCodeElement cf) {
        LinkedList mods = new LinkedList();
        if (cf.isNative()) {
            mods.add(new Native());
        }
        if (cf.isAbstract()) {
            mods.add(new Abstract());
        }
        if (cf.isPublic()) {
            mods.add(new Public());
        } else if (cf.isPrivate()) {
            mods.add(new Private());
        } else if (cf.isProtected()) {
            mods.add(new Protected());
        }
        if (cf.isFinal()) {
            mods.add(new Final());
        }
        if (cf.isSynchronized()) {
            mods.add(new Synchronized());
        }
        return (Modifier[]) mods.toArray(new Modifier[mods.size()]);
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
                .getFieldSpecification(0).getProgramVariable());

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
                        integerType, superArrayType, false));
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
                KeYJavaType integerType = getKeYJavaType(getServiceConfiguration()
                        .getNameInfo().getIntType());

                members.add(createImplicitArrayField(
                        ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE, new TypeRef(
                                integerType), true, parent));

                final recoder.service.NameInfo nameInfo = getServiceConfiguration()
                .getNameInfo();

                TypeReference booleanArrayTypeRef;
                if (base == PrimitiveType.JAVA_BOOLEAN && dimension == 1) {
                    booleanArrayTypeRef = parentReference;
                } else {
                    booleanArrayTypeRef = new TypeRef(getKeYJavaType(nameInfo
                            .getArrayType(nameInfo.getBooleanType())), 1);
                }
                members.add(createImplicitArrayField(
                        ImplicitFieldAdder.IMPLICT_ARRAY_TRA_INITIALIZED,
                        booleanArrayTypeRef, false, parent));

                // add methods
                // the only situation where base can be null is in case of a
                // reference type
                Expression defaultValue = (base != null ? base.getDefaultValue()
                        : NullLiteral.NULL);

                ListOfField fields = filterField(members);

                ProgramVariable length = len;// find("length", fields);

                if (arrayMethodBuilder == null) {
                    initArrayMethodBuilder();
                }
                final ProgramMethod prepare = arrayMethodBuilder.getPrepareArrayMethod(
                        parentReference, length, defaultValue, fields);

                members.add(arrayMethodBuilder
                        .getArrayInstanceAllocatorMethod(parentReference));
                members.add(prepare);
                members.add(arrayMethodBuilder.getCreateArrayHelperMethod(
                        parentReference, length, fields));
                members.add(arrayMethodBuilder.getCreateArrayMethod(parentReference,
                        prepare, fields));
                members.add(transientArrayMethodBuilder
                        .getCreateTransientArrayHelperMethod(parentReference, length,
                                fields));
                members.add(transientArrayMethodBuilder.getCreateTransientArrayMethod(
                        parentReference, length, prepare, fields));
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
                new LocationVariable(
                        new ProgramElementName(Recoder2KeYConverter.makeAdmissibleName(name),
                                Recoder2KeYConverter.makeAdmissibleName(prefix.getSort().name().toString())),
                                typeRef.getKeYJavaType(), prefix, isStatic), typeRef
                                .getKeYJavaType());
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
     * @return a ListOfField the includes all field specifications found int the
     *         field declaration of the given list
     */
    private ListOfField filterField(FieldDeclaration field) {
        ListOfField result = SLListOfField.EMPTY_LIST;
        ArrayOfFieldSpecification spec = field.getFieldSpecifications();
        for (int i = spec.size() - 1; i >= 0; i--) {
            result = result.prepend(spec.getFieldSpecification(i));
        }
        return result;
    }

    /**
     * extracts all field specifications out of the given list. Therefore it
     * descends into field declarations.
     * 
     * @param list
     *            the ExtList with the members of a type declaration
     * @return a ListOfField the includes all field specifications found int the
     *         field declaration of the given list
     */
    private ListOfField filterField(ExtList list) {
        ListOfField result = SLListOfField.EMPTY_LIST;
        Iterator it = list.iterator();
        while (it.hasNext()) {
            Object pe = it.next();
            if (pe instanceof FieldDeclaration) {
                result = result.prepend(filterField((FieldDeclaration) pe));
            }
        }
        return result;
    }

    private void initArrayMethodBuilder() {
        final KeYJavaType integerType = getKeYJavaType(getServiceConfiguration()
                .getNameInfo().getIntType());
        final KeYJavaType byteType = getKeYJavaType(getServiceConfiguration()
                .getNameInfo().getByteType());
        final KeYJavaType objectType = javaInfo().getJavaLangObject();
        arrayMethodBuilder = new CreateArrayMethodBuilder(integerType,
                objectType);
        transientArrayMethodBuilder = new CreateTransientArrayMethodBuilder(
                integerType, objectType, byteType);
    }

    private JavaInfo javaInfo() {
        return typeConverter != null ? typeConverter.getServices()
                .getJavaInfo() : null;
    }

}
