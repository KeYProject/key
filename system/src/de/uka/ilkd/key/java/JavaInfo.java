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

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Method;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.ImplicitFieldSpecification;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.SuperArrayDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.SpecificationElement;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.LRUCache;

/**
 * an instance serves as representation of a Java model underlying a DL
 * formula. This class provides calls to access the elements of the Java
 * model using the KeY datastructures only. Implementation specific
 * details like the use of Recoder is hidden in the field of type
 * {@link KeYProgModelInfo}. This class can be extended to provide further
 * services.
 */
public final class JavaInfo {


    public static class CacheKey {
        Object o1;
        Object o2;

        public CacheKey(KeYJavaType k1, KeYJavaType k2) {
            assert k1 != null && k2 != null;
            o1 = k1;
            o2 = k2;
        }

        public boolean equals(Object o) {
            if (o instanceof CacheKey) {
                final CacheKey snd = (CacheKey)o;
                return snd.o1.equals(o1) && snd.o2.equals(o2);
            }
            return false;
        }

        public int hashCode() {
            return o1.hashCode() + o2.hashCode();
        }

    }


    protected Services services;
    private KeYProgModelInfo kpmi;

    /**
     * the type of null
     */
    private KeYJavaType nullType = null;

    /**
     * as accessed very often caches:
     * KeYJavaType of
     *    java.lang.Object, java.lang.Clonable, java.io.Serializable
     * in </em>in this order</em>
     */
    protected KeYJavaType[] commonTypes = new KeYJavaType[3];

    //some caches for the getKeYJavaType methods.
    private HashMap<Sort, KeYJavaType> sort2KJTCache = null;
    private HashMap<Type, KeYJavaType> type2KJTCache = null;
    private HashMap<String, KeYJavaType> name2KJTCache = null;


    private LRUCache<CacheKey, ImmutableList<KeYJavaType>> commonSubtypeCache
    	= new LRUCache<CacheKey, ImmutableList<KeYJavaType>>(200);

    private int nameCachedSize = 0;
    private int sortCachedSize = 0;

    /**
     * The default execution context is for the case of program statements on
     * the top level. It is equivalent to a static class belonging the default
     * package. This should only be used when using KeY in academic mode, if
     * the verification conditions are generated they "must" start with a
     * {@link de.uka.ilkd.key.java.statement.MethodBodyStatement} or a
     * {@link de.uka.ilkd.key.java.statement.MethodFrame}, which contains a
     * valid execution context.
     */
    protected ExecutionContext defaultExecutionContext;

    protected boolean commonTypesCacheValid;

    /** caches the arrays' length attribute*/
    private ProgramVariable length;

    /** caches the program variable for {@code <inv>} */
    private ProgramVariable invProgVar;

    /** caches the observer for {@code <inv>} */
    private IObserverFunction inv;

    /** the name of the class used as default execution context */
    protected static final String DEFAULT_EXECUTION_CONTEXT_CLASS = "<Default>";
    protected static final String DEFAULT_EXECUTION_CONTEXT_METHOD = "<defaultMethod>";

    private HashMap<KeYJavaType,IObserverFunction> staticInvs = new LinkedHashMap<KeYJavaType,IObserverFunction>();


    /**
     * creates a new JavaInfo object by giving a KeYProgModelInfo to access
     * the Recoder SourceInfo and using the given {@link Services} object.
     */
    protected JavaInfo(KeYProgModelInfo kpmi, Services s) {
	this.kpmi 	= kpmi;
	services	= s;
    }

    protected JavaInfo(JavaInfo proto, Services s) {
	this ( proto.getKeYProgModelInfo().copy(), s );
	nullType  = proto.getNullType();
    }

    /**
     * returns the underlying KeYProgModelInfo providing access to the
     * Recoder structures.
     */
    public KeYProgModelInfo getKeYProgModelInfo(){
        return kpmi;
    }

    void setKeYProgModelInfo(KeYProgModelInfo kpmi){
        this.kpmi = kpmi;
    }

    /**
     * convenience method that returns the Recoder-to-KeY mapping underlying
     * the KeYProgModelInfo of this JavaInfo
     */
    public KeYRecoderMapping rec2key() {
	return getKeYProgModelInfo().rec2key();
    }

    /**
     * copies this JavaInfo and uses the given Services object as the
     * Services object of the copied JavaInfo
     * @param serv the Services the copy will use and vice versa
     * @return a copy of the JavaInfo
     */
    public JavaInfo copy(Services serv) {
 	return new JavaInfo(this, serv);
    }

    /**
     * Don't make this method public, use <code>Services</code>
     * instead
     *
     * returns the TypeConverter to translate program parts to their
     * logic equivalent
     */
    private TypeConverter getTypeConverter() {
        return services.getTypeConverter();
    }

    /**
     * returns the services associated with this JavaInfo
     */
    public Services getServices(){
	return services;
    }

    //------------------- common services ----------------------

    /**
     * returns the full name of a given {@link
     * de.uka.ilkd.key.java.abstraction.KeYJavaType}.
     * @param t the KeYJavaType including the package prefix
     * @return the full name
     */
    public String getFullName(KeYJavaType t) {
        return kpmi.getFullName(t);
    }

    /**
     * creates a new TypeReference for the given KeYJavaType
     */
    public TypeReference createTypeReference(KeYJavaType kjt) {
        return new TypeRef(kjt);
    }

    public void resetCaches(){
	sort2KJTCache = null;
	type2KJTCache = null;
	name2KJTCache = null;
	nameCachedSize = 0;
	sortCachedSize = 0;
    }

    /**
     * looks up the fully qualifying name given by a String
     * in the list of all available
     * KeYJavaTypes in the Java model
     * @param fullName the String
     * @return the KeYJavaType with the name of the String
     */
    public KeYJavaType getTypeByName(String fullName) {
        fullName = translateArrayType(fullName);
        if(name2KJTCache == null || kpmi.rec2key().size() > nameCachedSize){
            buildNameCache();
        }
        return name2KJTCache.get(fullName);
    }

    /**
     * caches all known types using their qualified name as retrieval key
     */
    private void buildNameCache() {
        nameCachedSize = kpmi.rec2key().size();
        name2KJTCache = new LinkedHashMap<String, KeYJavaType>();
        for (final Object o : kpmi.allElements()) {
            if (o != null && o instanceof KeYJavaType){
                final KeYJavaType oKJT = (KeYJavaType)o;
                if (oKJT.getJavaType() instanceof ArrayType) {
                    final ArrayType at = (ArrayType) oKJT.getJavaType();
                    name2KJTCache.put(at.getFullName(), oKJT);
                    name2KJTCache.put(at.getAlternativeNameRepresentation(), oKJT);
                } else {
                    name2KJTCache.put(getFullName(oKJT), oKJT);
                }
            }
        }
    }


    /**
     * checks if name refers to a package
     * @param name a String with the name to be checked
     * @return true iff name refers to a package
     */
    public boolean isPackage(String name) {
	return kpmi.isPackage(name);
    }

    /**
     * Translates things like int[] into [I, etc.
     */
    private String translateArrayType(String s) {
        if ("byte[]".equals(s))
            return "[B";
        else if ("int[]".equals(s))
            return "[I";
        else if ("long[]".equals(s))
            return "[J";
        else if ("short[]".equals(s))
            return "[S";
        else if ("char[]".equals(s))
            return "[C";
// Strangely, this one is not n
//        else if ("boolean[]".equals(s))
//            return "[Z";
// Not sure if these are needed, commented out for efficiency
//        else if ("char[]".equals(s))
//            return "[C";
//        else if ("double[]".equals(s))
//            return "[D";
//        else if ("float[]".equals(s))
//            return "[F";
//      else if ("\\real[]".equals(s))
//            return "[R";
//      else if ("\\bigint[]".equals(s))
//            return "[Y";
	return s;
    }

    /**
     * looks up a KeYJavaType with given name. If the name is a fully
     * qualifying name with package prefix an element with this full name is
     * taken. In case of an unqualified name to which no type is found in the default package,
     * the type is looked for in package <code>cjava.lang</code>
     * @param className the fully qualified class name (or an unqualified name from package java.lang)
     * @return a class matching the name
     */
    public KeYJavaType getTypeByClassName(String className) {
        return getTypeByClassName(className, null);
    }

    /**
     * returns a type declaration with the full name of the given String fullName
     */
    public TypeDeclaration getTypeDeclaration(String fullName) {
        return (TypeDeclaration)getTypeByName(fullName).getJavaType();
    }


    /**
     * returns all known KeYJavaTypes of the current
     * program type model
     * @return all known KeYJavaTypes of the current
     * program type model
     */
    public Set<KeYJavaType> getAllKeYJavaTypes() {
	final Set<KeYJavaType> result  = new LinkedHashSet<KeYJavaType>();
        for (final Object o : kpmi.allElements()) {
	    if (o instanceof KeYJavaType) {
	        result.add((KeYJavaType)o);
	    }
	}
	return result;
    }


    public KeYJavaType getPrimitiveKeYJavaType(PrimitiveType type) {
	assert type != null;
	KeYJavaType result = null;
	if(type2KJTCache != null) {
	    result = type2KJTCache.get(type);
	}

	if(result == null) {
	    Name ldtName = type.getCorrespondingLDTName();
	    final Namespace sorts = services.getNamespaces().sorts();
	    final Sort sort;
	    sort = (Sort) sorts.lookup(ldtName);
	    assert sort != null : "could not find sort for type: " + type;
	    result = new KeYJavaType(type, sort);
	    if(type2KJTCache != null) {
		type2KJTCache.put(type, result);
	    }
	}

	return result;
    }


    /**
     * returns a primitive KeYJavaType matching the given typename.
     */
    public KeYJavaType getPrimitiveKeYJavaType(String typename) {
	PrimitiveType type = PrimitiveType.getPrimitiveType(typename);
	if(type != null) {
	    return getPrimitiveKeYJavaType(type);
	} else {
	    return null;
	}
    }

    /**
     * returns a KeYJavaType (either primitive of object type) having the
     * full name of the given String fullName
     * @param fullName a String with the type name to lookup
     */
    public KeYJavaType getKeYJavaType(String fullName) {
        KeYJavaType result = getPrimitiveKeYJavaType(fullName);
        return (result == null ?
            getTypeByClassName(fullName) :
            result);
    }


    /**
     * returns true iff the given subType KeYJavaType is a sub type of the
     * given KeYJavaType superType.
     */
    public boolean isSubtype(KeYJavaType subType, KeYJavaType superType) {
        return kpmi.isSubtype(subType, superType);
    }

    public boolean isInterface(KeYJavaType t){
        return (t.getJavaType() instanceof InterfaceDeclaration);
    }


    /**
     * Checks whether the type is declared as final.
     * Returns false for all primitive and array types.
     * @param kjt
     * @return
     */
    public boolean isFinal(KeYJavaType kjt) {
        return kpmi.isFinal(kjt);
    }

    public static boolean isPrivate(KeYJavaType kjt) {
        final Type t = kjt.getJavaType();
        if (t instanceof ClassType) {
            return ((ClassType)t).isPrivate();
        } else if (t instanceof ArrayType) {
            final ArrayType at = (ArrayType) t;
            return isPrivate(at.getBaseType().getKeYJavaType());
        } else // primitive type or null
            return true;
    }

    public static boolean isVisibleTo(SpecificationElement ax, KeYJavaType visibleTo) {
        final KeYJavaType kjt = ax.getKJT();
        // elements of private types are not visible
        if (isPrivate(kjt)) return kjt.equals(visibleTo);
        //TODO: package information not yet available
        // BUGFIX: package-private is understood as private (see bug #1268)
        final boolean visibleToPackage = false;
        final VisibilityModifier visibility = ax.getVisibility();
        if (VisibilityModifier.isPublic(visibility))
            return true;
        if (VisibilityModifier.allowsInheritance(visibility))
            return visibleTo.getSort().extendsTrans(kjt.getSort()) || visibleToPackage;
        if (VisibilityModifier.isPackageVisible(visibility))
            return visibleToPackage;
        else
            return kjt.equals(visibleTo);
    }


    /**
     * returns a KeYJavaType having the given sort
     */
     public KeYJavaType getKeYJavaType(Sort sort) {
	 if(sort2KJTCache == null || kpmi.rec2key().size() > sortCachedSize){
	     sortCachedSize = kpmi.rec2key().size();
	     sort2KJTCache = new LinkedHashMap<Sort, KeYJavaType>();
	     for (final Object o : kpmi.allElements()) {
	         if (o instanceof KeYJavaType){
	             final KeYJavaType oKJT = (KeYJavaType)o;
	             if(sort2KJTCache.containsKey(oKJT.getSort())) {
	                 sort2KJTCache.remove(oKJT.getSort()); //XXX
	             }
	             sort2KJTCache.put((oKJT).getSort(), oKJT);
	         }
	     }
	 }

	 // lookup for primitive ldts
	 KeYJavaType result = sort2KJTCache.get(sort);
	 if(result == null) {
	     Name n = sort.name();
	     PrimitiveType pt = PrimitiveType.getPrimitiveTypeByLDT(n);
	     if(pt != null) {
	         return getPrimitiveKeYJavaType(pt);
	     }
	 }
    return result;
     }


    /**
     * returns the KeYJavaType belonging to the given Type t
     */
    public KeYJavaType getKeYJavaType(Type t) {
	if(type2KJTCache == null) {
	    type2KJTCache = new LinkedHashMap<Type, KeYJavaType>();
	    for (final Object o : kpmi.allElements()) {
		if (o instanceof KeYJavaType) {
		    final KeYJavaType oKJT = (KeYJavaType)o;
		    type2KJTCache.put(oKJT.getJavaType(), oKJT);
		}
	    }
	}
	if(t instanceof PrimitiveType) {
	    return getPrimitiveKeYJavaType((PrimitiveType)t);
	} else {
	    return type2KJTCache.get(t);
	}
    }

    /**
     * returns all methods from the given Type
     */
    public ImmutableList<Method> getAllMethods(KeYJavaType kjt) {
        return kpmi.getAllMethods(kjt);
    }

    /**
     * returns all locally declared methods from the given Type
     */
    public ImmutableList<Method> getMethods(KeYJavaType kjt) {
        return kpmi.getMethods(kjt);
    }

    /**
     * returns all methods from the given Type as IProgramMethods
     */
    public ImmutableList<IProgramMethod> getAllProgramMethods(KeYJavaType kjt) {
        return kpmi.getAllProgramMethods(kjt);
    }

    /**
     * returns all methods declared in the given Type as IProgramMethods
     */
    public ImmutableList<IProgramMethod> getAllProgramMethodsLocallyDeclared(KeYJavaType kjt) {
        return kpmi.getAllProgramMethodsLocallyDeclared(kjt);
    }


    public ImmutableList<IProgramMethod> getConstructors(KeYJavaType kjt) {
	return kpmi.getConstructors(kjt);
    }

    public IProgramMethod getConstructor(KeYJavaType kjt,
	    				ImmutableList<KeYJavaType> signature) {
	return kpmi.getConstructor(kjt, signature);
    }

    /**
     * returns the program methods defined in the given KeYJavaType with name
     * m and the list of types as signature of the method
     * @param classType the KeYJavaType of the class where to look for the
     *  method
     * @param methodName the name of the method
     * @param signature a IList<Type> with the arguments types
     * @param context the KeYJavaType of the class context from <em>where</em>
     *  the method is called
     * @return a matching program method
     */
    public IProgramMethod getProgramMethod(KeYJavaType classType,
            			          String methodName,
            			          ImmutableList<? extends Type> signature,
            			          KeYJavaType context) {
        return kpmi.getProgramMethod(classType, methodName, signature, context);
    }


    public IProgramMethod getToplevelPM(KeYJavaType kjt,
	    			       String methodName,
	    			       ImmutableList<KeYJavaType> sig) {
	for(KeYJavaType sup : getAllSupertypes(kjt).removeAll(kjt)) {
	    final IProgramMethod result = getToplevelPM(sup, methodName, sig);
	    if(result != null) {
		return result;
	    }
	}
	return getProgramMethod(kjt, methodName, sig, kjt);
    }


    public IProgramMethod getToplevelPM(KeYJavaType kjt, IProgramMethod pm) {
	final String methodName = pm.getName();
    	final ImmutableList<KeYJavaType> sig
		= ImmutableSLList.<KeYJavaType>nil()
		                 .append(pm.getParamTypes()
		                	   .toArray(
		                      new KeYJavaType[pm.getNumParams()]));
	return getToplevelPM(kjt, methodName, sig);
    }


    public Term getProgramMethodTerm(Term prefix,
	    			     String methodName,
				     Term[] args,
				     String className) {
	ImmutableList<KeYJavaType> sig = ImmutableSLList.<KeYJavaType>nil();
	KeYJavaType clType = getTypeByClassName(className);
	for(int i=0; i < args.length; i++) {
        sig = sig.append(getServices().getTypeConverter()
                .getKeYJavaType(args[i]));
	}	
	IProgramMethod pm   = getProgramMethod(clType, methodName, sig, clType);
	if(pm == null) {
	    throw new IllegalArgumentException("Program method "+methodName
					       +" in "+className+" not found.");
	}
	Term[] subs = new Term[pm.getHeapCount(services)*pm.getStateCount() + args.length + (pm.isStatic() ? 0 : 1)];
	int offset = 0;
	for(LocationVariable heap : HeapContext.getModHeaps(services, false)) {
		if(offset >= pm.getHeapCount(services)) {
			break;
		}
		subs[offset++] = services.getTermBuilder().var(heap);
	}
	if(!pm.isStatic()) {
	  subs[offset++] = prefix;
	}
	for(int i=0; offset < subs.length; i++, offset++) {
        subs[offset] = args[i];
	}
	className = translateArrayType(className);
	assert pm.getReturnType() != null;
	if(pm.isVoid()) {
	    throw new IllegalArgumentException("Program method "+methodName
					       +" in "+className+" must have"
					       +" a non-void type.");
	}
	return services.getTermBuilder().tf().createTerm(pm, subs);
    }


    /**
     * returns all direct supertypes (local declared types in extends and
     * implements) if extends is not given explict java.lang.Object is added
     * (it is not added for interfaces)
     */
    public ImmutableList<KeYJavaType> getDirectSuperTypes(KeYJavaType type) {
        final ClassType javaType = (ClassType) type.getJavaType();

        ImmutableList<KeYJavaType> localSupertypes = javaType.getSupertypes();

        if (!javaType.isInterface()) {
            final Iterator<KeYJavaType> it = localSupertypes.iterator();
            boolean found = false;
            while (it.hasNext()) {
                KeYJavaType keYType = it.next();
                if (!((ClassType)keYType.getJavaType()).isInterface()) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                localSupertypes = localSupertypes.prepend(getJavaLangObject());
            }

        }
        return localSupertypes;
    }


    /**
     * retrieves the direct extended superclass for the given class
     * @param type the KeYJavaType of the type whose superclass
     * has to be determined
     * @return KeYJavaType of the extended supertype
     */
    public KeYJavaType getSuperclass(KeYJavaType type) {
	KeYJavaType result = null;
	final ClassType javaType = (ClassType) type.getJavaType();

	if (javaType.isInterface()) {
	    return null;
	}

	final ImmutableList<KeYJavaType> localSupertypes = javaType.getSupertypes();
	final Iterator<KeYJavaType> it = localSupertypes.iterator();
	while (result == null && it.hasNext()) {
	    final KeYJavaType keYType = it.next();
	    if (!((ClassType)keYType.getJavaType()).isInterface()) {
		result = keYType;
	    }
	}

	if(result == null && ((ClassDeclaration) javaType).isAnonymousClass()){
        for (Sort sort : type.getSort().extendsSorts()) {
            Sort s = sort;
            if (!((ClassType) getKeYJavaType(s).getJavaType()).isInterface()) {
                return getKeYJavaType(s);
            }
        }
	}

	if (result == null) {
	    result = getJavaLangObject();
	}

        return result;
    }


    /**
     * returns the program method defined in the KeYJavaType of the program
     * variable clv, with the name m, and the KeYJavaTypes of the given array
     * of program variables as signatures.
     * @param classType the KeYJavaType of the class where to look for the
     *  method
     * @param methodName the name of the method
     * @param args an array of ProgramVariables as the arguments of the
     * method
     * @param context the KeYJavaType of the class context from <em>where</em>
     *  the method is called
     * @return a matching program method
     */
    public IProgramMethod getProgramMethod(KeYJavaType classType,
	    				  String methodName,
	    				  ProgramVariable[] args,
	    				  KeYJavaType context){
        ImmutableList<Type> types = ImmutableSLList.<Type>nil();
        for (int i = args.length - 1; i>=0; i--) {
            types = types.prepend(args[i].getKeYJavaType());
        }
        return getProgramMethod(classType, methodName, types, context);
    }

    /** gets an array of expression and returns a list of types */
    private ImmutableList<KeYJavaType> getKeYJavaTypes(ImmutableArray<? extends Expression> args) {
	ImmutableList<KeYJavaType> result = ImmutableSLList.<KeYJavaType>nil();
	if (args != null) {
	    for (int i = args.size()-1; i >= 0 ; i--) {
		final Expression argument = args.get(i);
		result = result.prepend
		    (getTypeConverter().getKeYJavaType(argument));
	    }
	}
	return result;
    }


    /**
     * retrieves the signature according to the given expressions
     * @param arguments ArrayOf<Expression> of which we try to construct a
     * signature
     * @return the signature
     */
    public ImmutableList<KeYJavaType> createSignature(ImmutableArray<? extends Expression> arguments) {
	return getKeYJavaTypes(arguments);
    }

    /**
     * retrieves all attributes locally declared in class <tt>cl</tt>
     * (inclusive the implicit attributes)
     * The returned list is in source code order.
     * @param classDecl the ClassDeclaration whose attributes shall be collected
     * @return all attributes declared in class <tt>cl</tt>
     */
    public ImmutableList<Field> getAllFields(TypeDeclaration classDecl) {
	return filterLocalDeclaredFields(classDecl, Filter.TRUE);
    }

    /**
     * retrieves all implicit attributes locally declared in the given class
     * The returned list is in source code order.
     * @param cl the ClassDeclaration where to look for the implicit
     * attributes
     * @return all implicit attributes declared in <tt>cl</tt>
     */
    public ImmutableList<Field> getImplicitFields(ClassDeclaration cl) {
        return filterLocalDeclaredFields(cl, Filter.IMPLICITFIELD);
    }

    /**
     * retrieves all attributes locally declared in class <tt>cl</tt>
     * (inclusive the implicit attributes) satisfying the given filter
     * The returned list is in source code order.
     * @param classDecl the ClassDeclaration whose attributes shall be collected
     * @param filter the Filter to be satisifed by the attributes to
     * be returned
     * @return all attributes declared in class <tt>cl</tt> satisfying the
     * given filter
     */
    private ImmutableList<Field> filterLocalDeclaredFields(TypeDeclaration classDecl,
            Filter filter) {
        ImmutableList<Field> fields = ImmutableSLList.<Field>nil();
        final ImmutableArray<MemberDeclaration> members = classDecl.getMembers();
        for (int i = members.size()-1; i>=0; i--) {
            final MemberDeclaration member = members.get(i);
            if (member instanceof FieldDeclaration) {
        	final ImmutableArray<FieldSpecification> specs =
        	    ((FieldDeclaration)member).getFieldSpecifications();
        	for (int j = specs.size()-1; j>=0; j--) {
        	    final FieldSpecification fieldSpec = specs.get(j);
                    if (filter.isSatisfiedBy(fieldSpec)) {
                        fields = fields.prepend(fieldSpec);
                    }
        	}
            }
        }
        return fields;
    }

    //----------------- parsing services --------------------------

    /**
     * reads a Java block given as a string java as it was in the given
     * TypeDeclaration asIn.
     */
     public JavaBlock readJavaBlock(String java, TypeDeclaration asIn) {
        ClassDeclaration cd = null;
        if (asIn instanceof ClassDeclaration) {
            cd = (ClassDeclaration)asIn;
        } else {
            Debug.out("Reading Java Block from an InterfaceDeclaration:"
                      +" Not yet implemented.");
        }
        final NamespaceSet nss = services.getNamespaces().copy();
        nss.startProtocol();
        final JavaBlock block = kpmi.readBlock(java, cd, nss);
        // if we are here everything is fine and we can add the
        // changes (may be new array types)
        services.getNamespaces().addProtocolled(nss);
        return block;
    }

    /**
     * reads a Java block given as a String
     */
    public JavaBlock readJavaBlock(String java) {
        NamespaceSet nss = services.getNamespaces().copy();
        nss.startProtocol();
        final JavaBlock block = kpmi.readJavaBlock(java, nss);
        // if we are here everything is fine nad wen can add the
        // changes (may be new array types)
        services.getNamespaces().addProtocolled(nss);
        return block;
    }

    /**
     * reads a Java statement not necessarily a block
     */
    public ProgramElement readJava(String java) {
        return ((StatementBlock)readJavaBlock("{"+java+"}")
		.program()).getChildAt(0);
    }

    /**
     * retrieves a field with the given name out of the list
     * @param programName a String with the name of the field to be looked for
     * @param fields the IList<Field> where we have to look for the field
     * @return the program variable of the given name or null if not
     * found
     */
    private final ProgramVariable find(String programName,
                                       ImmutableList<Field> fields) {
        for (Field field1 : fields) {
            Field field = field1;
            if (programName.equals(field.getProgramName())) {
                return (ProgramVariable)
                        field.getProgramVariable();
            }
        }
	return null;
    }

    /**
     * extracts all fields out of fielddeclaration
     * @param field the FieldDeclaration of which the field
     * specifications have to be extracted
     * @return a IList<Field> the includes all field specifications found
     * int the field declaration of the given list
     */
    private final ImmutableList<Field> getFields(FieldDeclaration field) {
	ImmutableList<Field> result = ImmutableSLList.<Field>nil();
	final ImmutableArray<FieldSpecification> spec = field.getFieldSpecifications();
	for (int i = spec.size()-1; i>=0; i--) {
	    result = result.prepend(spec.get(i));
	}
	return result;
    }

    /**
     * extracts all field specifications out of the given
     * list. Therefore it descends into field declarations.
     * @param list the ArrayOf<MemberDeclaration> with the members of a
     * type declaration
     * @return a IList<Field> the includes all field specifications found
     * int the field declaration of the given list
     */
    private ImmutableList<Field> getFields(ImmutableArray<MemberDeclaration> list) {
	ImmutableList<Field> result = ImmutableSLList.<Field>nil();
	for (int i = list.size()-1; i >= 0; i--) {
	    final MemberDeclaration pe = list.get(i);
	    if (pe instanceof FieldDeclaration) {
		result = result.append
		    (getFields((FieldDeclaration)pe));
	    }
	}
	return result;
    }

    /**
     * returns the programvariable for the specified attribute. The attribute
     * has to be fully qualified, i.e. <tt>declarationType::attributeName</tt>
     * @param fullyQualifiedName the String with the fully qualified attribute
     * name
     * @return an attribute program variable of the given name
     * @throws IllegalArgumentException if the given name is not fully
     * qualified
     */
    public ProgramVariable getAttribute(String fullyQualifiedName) {
        final int idx = fullyQualifiedName.indexOf("::");

        if (idx == -1) {
            throw new IllegalArgumentException(fullyQualifiedName +
                    " is not a fully qualified attribute name");
        }

        return getAttribute(fullyQualifiedName.substring(idx+2),
			    fullyQualifiedName.substring(0, idx));
    }


    /**
     * returns the programvariable for the specified attribute declared in
     * the specified class
     * @param programName the String with the name of the attribute
     * @param qualifiedClassName the String with the full (inclusive package) qualified
     * class name
     * @return the attribute program variable of the given name
     * @throws IllegalArgumentException if the qualified class name is empty or
     * null
     * @throws UnknownJavaTypeException if the qualified name refers to an unknown type
     */
    public ProgramVariable getAttribute(String programName,
            String qualifiedClassName) {
    	if (qualifiedClassName == null || qualifiedClassName.length() == 0) {
    		throw new IllegalArgumentException("Missing qualified classname");
    	}

    	KeYJavaType kjt = null;
    	try {
	    kjt = getTypeByClassName(qualifiedClassName);
    	} catch (Exception e) {
    		if (qualifiedClassName.endsWith("]")) {
    			readJavaBlock("{" + qualifiedClassName + " k;}");
    			kjt = getKeYJavaType(qualifiedClassName);
    		}
    	}

    	if (kjt == null) {
    		throw new UnknownJavaTypeException("Java type '" + qualifiedClassName + "' not known.");
    	}

    	return getAttribute(programName, kjt);
    }


    /**
     * returns the program variable representing the attribute of the given
     * name declared locally in class <tt>classType</tt>
     * @return the attribute of the given name declared in <tt>classType</tt>
     */
    public ProgramVariable getAttribute(final String name,
					KeYJavaType classType) {
	if (classType.getJavaType() instanceof ArrayDeclaration) {
	    ProgramVariable res = find(name,
		    getFields(((ArrayDeclaration) classType.getJavaType())
		            .getMembers()));
	    if (res == null) {
		return getAttribute(name, getJavaLangObject());
	    }
	    return res;
	} else {
	    final ImmutableList<Field> list = kpmi
		    .getAllFieldsLocallyDeclaredIn(classType);
	    for (Field aList : list) {
		final Field f = aList;
		if (f != null
		        && (f.getName().equals(name) || f.getProgramName()
		                .equals(name))) {
		    return (ProgramVariable) f
			    .getProgramVariable();
		}
	    }
	}
	return null;
    }

    /**
     * returns an attribute named <tt>attributeName</tt> declared locally
     * in object type <tt>s</tt>
     */
    public ProgramVariable getAttribute(String attributeName, Sort s) {
	assert s.extendsTrans(objectSort());
        return getAttribute(attributeName, getKeYJavaType(s));
    }

    /**
     * returns a list of all attributes with the given program name
     * declared in one of <tt>type</tt>'s sub- or supertype including
     * its own attributes
     * <strong>Attention:</strong>
     *   The type must not denote the null type
     * </ol>
     *
     * @param programName the String with name of the attribute as declared
     * in a program
     * @param type the KeYJavaType specifying the part of the hierarchy
     * where to look for
     * @return list of found attributes with name <tt>programName</tt>
     */
    public ImmutableList<ProgramVariable> getAllAttributes(String programName,
                                                  KeYJavaType type) {
        ImmutableList<ProgramVariable> result =
            ImmutableSLList.<ProgramVariable>nil();

	if (!(type.getSort().extendsTrans(objectSort()))) {
	    return result;
	}

        if (type.getJavaType() instanceof ArrayType) {
            ProgramVariable var = find(programName, getFields
                        (((ArrayDeclaration)type.getJavaType())
                         .getMembers()));
            if (var != null) { result = result.prepend(var); }
            var = getAttribute(programName, getJavaLangObject());
            if (var != null) { result = result.prepend(var); }
            return result;
        }


        // the assert statements below are not for fun, some methods rely
        // on the correct order
        ImmutableList<KeYJavaType> hierarchy = kpmi.getAllSubtypes(type);
        assert !hierarchy.contains(type);

        hierarchy = hierarchy.prepend(kpmi.getAllSupertypes(type));
        assert hierarchy.head() == type;


        final Iterator<KeYJavaType> it = hierarchy.iterator();
        while (it.hasNext()) {
	    KeYJavaType st = it.next();
	    if(st != null){
		final ProgramVariable var = getAttribute(programName, st);
		if (var != null) {
		    result = result.prepend(var);
		}
	    }
        }

        return result;
    }


    protected void fillCommonTypesCache() {
	if (commonTypesCacheValid) return;

	final String[] fullNames = new String[] {"java.lang.Object",
		"java.lang.Cloneable", "java.io.Serializable"};

	for (int i = 0; i<fullNames.length; i++) {
	    commonTypes[i] = getTypeByClassName(fullNames[i]);
	}
	commonTypesCacheValid = true;
    }

    /**
     * returns the KeYJavaType for class <tt>java.lang.Object</tt>
     */
    public KeYJavaType getJavaLangObject() {
        if (commonTypes[0] == null) {
            commonTypes[0] = getTypeByClassName("java.lang.Object");
        }
        return commonTypes[0];
    }


    /**
     * returns the KeYJavaType for class java.lang.Clonable
     */
    public KeYJavaType getJavaLangCloneable() {
        if (commonTypes[1] == null) {
            commonTypes[1] = getTypeByClassName("java.lang.Cloneable");
        }
        return commonTypes[1];
    }

    /**
     * returns the KeYJavaType for class <tt>java.io.Serializable</tt>
     */
    public KeYJavaType getJavaIoSerializable() {
        if (commonTypes[2] == null) {
            commonTypes[2] = getTypeByClassName("java.io.Serializable");
        }
        return commonTypes[2];
    }

    /**
     * returns the KeYJavaType for class java.lang.Object
     */
    public Sort objectSort() {
	try {
	    return getJavaLangObject().getSort();
	} catch(RuntimeException e) {//XXX
	    return null;
	}
    }

    /**
     * returns the KeYJavaType for class java.lang.Cloneable
     */
    public Sort cloneableSort() {
        return getJavaLangCloneable().getSort();
    }

    /**
     * returns the KeYJavaType for class java.io.Serializable
     */
    public Sort serializableSort() {
        return getJavaIoSerializable().getSort();
    }

    public Sort nullSort() {
	return getNullType().getSort();
    }

    /**
     * tests if sort represents java.lang.Object, java.lang.Cloneable or
     * java.io.Serializable
     */
    public boolean isAJavaCommonSort(Sort sort) {
        if (!commonTypesCacheValid) {
            fillCommonTypesCache();
        }
        for (KeYJavaType commonType : commonTypes) {
            if (commonType.getSort() == sort) {
                return true;
            }
        }
        return false;
    }

    /**
     * returns the KeYJavaType  representing the type of 'null'
     */
    public KeYJavaType getNullType() {
	if (nullType==null) {
	    nullType = getTypeByClassName("null");
	    Debug.assertTrue(nullType!=null
			 , "we should already have it in the map");
	}
	return nullType;
    }


    /**
     * returns the default execution context. This is equiavlent to executing the program
     * in a static method of a class placed in the default package
     * @return the default execution context
     */
    public ExecutionContext getDefaultExecutionContext() {
        if (defaultExecutionContext == null) {
            // ensure that default classes are available
            if (!kpmi.rec2key().parsedSpecial()) {
                readJava("{}");
            }
            final KeYJavaType kjt =
                getTypeByClassName(DEFAULT_EXECUTION_CONTEXT_CLASS);
            defaultExecutionContext =
                new ExecutionContext(new TypeRef(kjt), getToplevelPM(kjt, DEFAULT_EXECUTION_CONTEXT_METHOD, ImmutableSLList.<KeYJavaType>nil()), null);
        }
        return defaultExecutionContext;
    }


    /**
     * returns all proper subtypes of a given type
     * @param type the KeYJavaType whose subtypes are returned
     * @return list of all subtypes
     */
    public ImmutableList<KeYJavaType> getAllSubtypes(KeYJavaType type) {
        return kpmi.getAllSubtypes(type);
    }

    /**
     * returns all supertypes of a given type
     * @param type the KeYJavaType whose supertypes are returned
     * @return list of all supertypes
     */
    public ImmutableList<KeYJavaType> getAllSupertypes(KeYJavaType type) {
        if (type.getJavaType() instanceof ArrayType) {
            ImmutableList<KeYJavaType> res = ImmutableSLList.<KeYJavaType>nil();
            for (Sort s: getSuperSorts(type.getSort()))
                res = res.append(getKeYJavaType(s));
            return res;
        }
        return kpmi.getAllSupertypes(type);
    }

    private ImmutableList<Sort> getSuperSorts(Sort sort){
        ImmutableList<Sort> res = ImmutableSLList.<Sort>nil();
        final Sort object = getJavaLangObject().getSort();
        if (sort != object)
            for (Sort exsort: sort.extendsSorts(services)) {
                res = res.append(getSuperSorts(exsort)).append(exsort);
            }
        return res;
    }

    /**
     * looks up for a field of the given program name
     * visible <em>in</em> the specified class type belonging to the type
     * or one of its supertypes
     *
     * @param programName the String containing the name of the
     * field to be looked up. The name is in short notation,
     * i.e. not fully qualified
     * @param classType the KeYJavaType of the class used as context
     * @return the field of the given name
     */
    public ProgramVariable lookupVisibleAttribute(String programName,
                                                  KeYJavaType classType) {
        return find(programName, kpmi.getAllVisibleFields(classType));
    }


    /**
     * returns the list of all common subtypes of types <tt>k1</tt> and <tt>k2</tt>
     * (inclusive one of them if they are equal or subtypes themselves)
     * attention: <tt>Null</tt> is not a jav atype only a logic sort, i.e.
     * if <tt>null</tt> is the only element shared between <tt>k1</tt> and <tt>k2</tt>
     * the returned list will be empty
     *
     * @param k1 the first KeYJavaType denoting a class type
     * @param k2 the second KeYJavaType denoting a classtype
     * @return the list of common subtypes of types <tt>k1</tt> and <tt>k2</tt>
     */
    public ImmutableList<KeYJavaType> getCommonSubtypes(KeYJavaType k1, KeYJavaType k2) {
        final CacheKey ck = new CacheKey(k1, k2);
        ImmutableList<KeYJavaType> result = commonSubtypeCache.get(ck);

        if (result != null) {
            return result;
        }

        result = ImmutableSLList.<KeYJavaType>nil();

        if (k1.getSort().extendsTrans(k2.getSort())) {
            result = getAllSubtypes(k1).prepend(k1);
        } else if (k2.getSort().extendsTrans(k1.getSort())) {
            result = getAllSubtypes(k2).prepend(k2);
        } else {
            final ImmutableList<KeYJavaType> l1 = getAllSubtypes(k1);
            final ImmutableList<KeYJavaType> l2 = getAllSubtypes(k2);

            for (KeYJavaType aL1 : l1) {
                final KeYJavaType next = aL1;
                if (l2.contains(next)) {
                    result = result.prepend(next);
                }
            }
        }

        commonSubtypeCache.put(ck, result);
        return result;
    }

    /** returns the length attribute for arrays */
    public ProgramVariable getArrayLength() {
        if (length == null) {
            final SuperArrayDeclaration sad =
                (SuperArrayDeclaration)
                rec2key().getSuperArrayType().getJavaType();
            length =
                (ProgramVariable) sad.length().getVariables().
                get(0).getProgramVariable();
            assert "length".equals(length.name().toString()) : "Wrong array length";
        }

        return length;
    }

    /**
     * Returns the special symbol <code>&lt;inv&gt;</code> which stands for the class invariant of an object.
     * @see #getInvProgramVar()
     */
    public IObserverFunction getInv() {
	if(inv == null || inv.getHeapCount(services) != HeapContext.getModHeaps(services, false).size()) {
	    inv = new ObserverFunction("<inv>",
        			       Sort.FORMULA,
        			       null,
        			       services.getTypeConverter().getHeapLDT().targetSort(),
        			       getJavaLangObject(),
        			       false,
        			       new ImmutableArray<KeYJavaType>(),
        			       HeapContext.getModHeaps(services, false).size(),
        			       1);
	}
	return inv;
    }

    /**
     * Returns the special program variable symbol <code>&lt;inv&gt;</code>
     * which stands for the class invariant of an object.
     *
     * @see #getInv()
     */
    public ProgramVariable getInvProgramVar() {
        if(invProgVar == null) {
            ProgramElementName pen = new ProgramElementName("<inv>", "java.lang.Object");
            invProgVar = new LocationVariable(pen,
                                getPrimitiveKeYJavaType(PrimitiveType.JAVA_BOOLEAN),
                                getJavaLangObject(), false, true);
        }
        return invProgVar;
    }

    /**
     * Returns the special symbol <code>&lt;staticInv&gt;</code> which stands for the static invariant of a type.
     */
    public IObserverFunction getStaticInv(KeYJavaType target) {
        if (!staticInvs.containsKey(target))
            staticInvs.put(target, new ObserverFunction("<$inv>",
                           Sort.FORMULA,
                           null,
                           services.getTypeConverter().getHeapLDT().targetSort(),
                           target,
                           true,
                           new ImmutableArray<KeYJavaType>(),
        			       HeapContext.getModHeaps(services, false).size(),
                           1));
        return staticInvs.get(target);
    }

    /**
     * inner class used to filter certain types of program elements
     */
    static abstract class Filter {

        /** the universally satisfied filter */
        final static Filter TRUE = new Filter() {

            public boolean isSatisfiedBy(ProgramElement pe) {
                return true;
            }
        };

        /** this filter is satisfied if the given program element is an
         * instanceof ImplicitFieldSpecification
         */
        final static Filter IMPLICITFIELD = new Filter() {

            public boolean isSatisfiedBy(ProgramElement pe) {
                return pe instanceof ImplicitFieldSpecification;
            }
        };

        /**
         * decides whether the given program element fulfills the filter condition
         * or not
         * @param pe the ProgramElement to be filtered
         * @return true iff program element <tt>pe</tt> satisfies the filter
         * condition
         */
        public abstract boolean isSatisfiedBy(ProgramElement pe);
    }

    /**
     * retrieves the KeYJavaType of the given type name. If the type is not fully qualified,
     * it is looked for in the context of the <code>containerType</code> first and
     * then in the <code>java.lang</code>
     * package.
     * @param name the name of the type (if possible fully qualified)
     * @param containerType the KeYJavaType of the context in which the type should be resolved
     * @return the KeYJavaType of the given type or <code>null</code> if type name is unknown
     */
    public KeYJavaType getTypeByClassName(String name, KeYJavaType containerType) {
        KeYJavaType result = getTypeByName(name);
        if (result == null) {
            if (containerType != null) {
                   result = kpmi.resolveType(name, containerType);
            }

            if (result == null) {
                final int lastSep = (containerType == null ?
                        -1 : containerType.getFullName().lastIndexOf('.'));

                // try if class is in same package
                if (lastSep >= 0) {
                    result = getTypeByClassName(
                            containerType.getFullName().substring(0, lastSep) +
                            "." + name);
                }

                if (result == null) {
                    return getTypeByName("java.lang." + name);
                }
            }
        }
        return result;
    }
}