// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;

import java.util.*;

import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
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
public class JavaInfo {


    public class CacheKey {
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


    private Services services;
    private KeYProgModelInfo  kpmi;
    private String javaSourcePath;

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
    private KeYJavaType[] commonTypes = new KeYJavaType[4];

    //some caches for the getKeYJavaType methods.
    private HashMap<Sort, KeYJavaType> sort2KJTCache = null;
    private HashMap<Type, KeYJavaType> type2KJTCache = null;
    private HashMap<String, KeYJavaType> name2KJTCache = null;

    // the simple name lookup is errorprone and should be removed soon
    // where it is used, force to specify a context class for unique type 
    // resolution
    private HashMap<String, Object> sName2KJTCache = null;
    
    private LRUCache commonSubtypeCache = new LRUCache(200);
    
    private int nameCachedSize = 0;
    private int sNameCachedSize = 0;
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
    private ExecutionContext defaultExecutionContext;
                
    private LocationVariable defaultMemoryArea;    
    private LocationVariable immortalMemoryArea;    
    
    /**
     * a term with the constant 'null'
     */
    private Term nullConst=null;
    private boolean commonTypesCacheValid;
    
    /** caches the predicate used to express a lega java state */
    private Function legalHeapStructure;
    
    /** caches the arrays' length attribute*/
    private ProgramVariable length;
    
    /** the name of the class used as default execution context */
    static final String DEFAULT_EXECUTION_CONTEXT_CLASS = "<Default>";

	
    /**
     * creates a new JavaInfo object by giving a KeYProgModelInfo to access
     * the Recoder SourceInfo and using the given {@link Services} object.
     */
    JavaInfo(KeYProgModelInfo kpmi, Services s) {
	this.kpmi 	= kpmi;
	services	= s;	 
    }

    private JavaInfo(JavaInfo proto, Services s) {
	this ( proto.getKeYProgModelInfo().copy(), s );
	nullType  = proto.getNullType();
	nullConst = proto.getNullConst();
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
     * returns the predicate expressing that we are in a state reachable by executing a
     * a java program
     */
    public Function getInReachableState() {
        if (legalHeapStructure == null) {
            legalHeapStructure = (Function) services.getNamespaces().lookup(new Name("inReachableState"));
            if (legalHeapStructure == null) {
                throw new RuntimeException("Legal pointer structure predicate not found.");
            }
        } 
        return legalHeapStructure;        
    }

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
	sName2KJTCache = null;
	nameCachedSize = 0;
	sNameCachedSize = 0;
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
        return (KeYJavaType) name2KJTCache.get(fullName);
    }

    /**
     * caches all known types using their qualified name as retrieval key 
     */
    private void buildNameCache() {
        nameCachedSize = kpmi.rec2key().size();
        name2KJTCache = new HashMap();
        Iterator it = (kpmi.allElements()).iterator();
        while (it.hasNext()) {
            Object o = it.next();
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
     * Translates things like int[], jint[] into [I, etc.
     */
    private String translateArrayType(String s) {
        if ("jbyte[]".equals(s) || "byte[]".equals(s))
            return "[B";
        else if ("jint[]".equals(s) || "int[]".equals(s))
            return "[I";
        else if ("jlong[]".equals(s) || "long[]".equals(s))
            return "[J";
        else if ("jshort[]".equals(s) || "short[]".equals(s))
            return "[S";
        else if ("jchar[]".equals(s) || "char[]".equals(s))
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
	return s;
    }

    /**
     * looks up a KeYJavaType with given name. If the name is a fully
     * qualifying name with package prefix an element with this full name is
     * taken. If the name does not contain a full package prefix some
     * KeYJavaType with this short name is taken.     
     * @param className the name to look for (either full or short)
     * @return a class matching the name
     */
    public KeYJavaType getTypeByClassName(String className) {
	KeYJavaType result = getTypeByName(className);
	className = translateArrayType(className);
        /* TODO: get rid of this short name thing; introduce second parameter
                 with the context in which to look for
         */
        if (result == null) {
	    final int dotpos = className.lastIndexOf(".");
            String shortName = className.substring(dotpos+1);
	    if(sName2KJTCache == null){
		buildShortNameCache();
	    }
	    result = (KeYJavaType) sName2KJTCache.get(shortName);
	}
	if(result != null){
	    Debug.out("javaInfo: type found (className, type):",
		      className, result);
	} else {
	    //this is for the case that the cache has been established to early
	    //(i.e. when not all types were known) 
	    if (kpmi.rec2key().size() > sNameCachedSize){
		sName2KJTCache = null;
		return getTypeByClassName(className);
	    }
            // maybe a not yet known array type
            if(className.endsWith("]")){
                readJavaBlock("{" + className + " k;}");
                result = getKeYJavaType(className);
                if(result!=null) return result;
            }
	    Debug.out("javaInfo: type not found. Looked for:", className);
	    throw new RuntimeException("TYPE NOT FOUND: " + className);
	}
	return result;
    }

    /**
     * caches all known types according to their short name
     */
    private void buildShortNameCache() {
        sName2KJTCache = new HashMap<String, Object>();
        sNameCachedSize = kpmi.rec2key().size();
        final HashSet<String> duplicates = new HashSet<String>();
        final Iterator it = kpmi.allElements().iterator();        
        while (it.hasNext()) {
            Object o = it.next();
            if (o != null && o instanceof KeYJavaType){
                KeYJavaType t = (KeYJavaType)o;                
                String name = getFullName(t);
                //TODO array types [[I vs. int[]
                int pos     = name.lastIndexOf(".");
                final String shortName = name.substring(pos+1);
                if (!sName2KJTCache.containsKey(shortName) && 
                        !duplicates.contains(shortName)) {
                    sName2KJTCache.put(shortName, o);
                } else {
                    duplicates.add(shortName);
                    sName2KJTCache.remove(shortName);
                }
            }
        }
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
	final Set<KeYJavaType> result  = new HashSet<KeYJavaType>();
	final Iterator it = kpmi.allElements().iterator();
        while (it.hasNext()) {
	    final Object o = it.next();     
	    if (o instanceof KeYJavaType) {		
	        result.add((KeYJavaType) o);
	    }
	}
	return result;
    }

    /**
     * returns a primitive KeYJavaType matching the given typename making use
     * of the LDTs of the current type converter in the services.
     */
    public KeYJavaType getPrimitiveKeYJavaType(String typename) {
        ListOfLDT models = getTypeConverter().getModels();
        final IteratorOfLDT ldtIterator = models.iterator();
        while (ldtIterator.hasNext()) {
            final LDT model = ldtIterator.next();           
            if (model.javaType() != null && 
                    model.javaType().getFullName().equals(typename)) {
                return model.getKeYJavaType(model.javaType());
            }
        }
        return null;
    }

    /**
     * returns a KeYJavaType (either primitive of object type) having the
     * full name of the given String fullName 
     * @param fullName a String with the type name to lookup 
     */
    public KeYJavaType getKeYJavaType(String fullName) {
        KeYJavaType result = getPrimitiveKeYJavaType(fullName);
        return (result == null ?
            (KeYJavaType)getTypeByClassName(fullName) :
            result);
    }


    /**
     * this is an alias for getTypeByClassName
     */
    public KeYJavaType getKeYJavaTypeByClassName(String className) {
        return getTypeByClassName(className);
    }


    /**
     * returns true iff the given subType KeYJavaType is a sub type of the
     * given KeYJavaType superType.
     */
    public boolean isSubtype(KeYJavaType subType, KeYJavaType superType) {
        return kpmi.isSubtype(subType, superType);
    }

    /** 
     * returns a KeYJavaType having the given sort
     */
     public KeYJavaType getKeYJavaType(Sort sort) {
	 if(sort2KJTCache == null || kpmi.rec2key().size() > sortCachedSize){
	     sortCachedSize = kpmi.rec2key().size();
	     sort2KJTCache = new HashMap<Sort, KeYJavaType>();
	     Iterator it = kpmi.allElements().iterator();
	     while (it.hasNext()) {
		 Object o = it.next();
		 if (o instanceof KeYJavaType){
                     final KeYJavaType oKJT = (KeYJavaType)o;
                     sort2KJTCache.put((oKJT).getSort(), oKJT);
		 }
	     }
	 }	
	 KeYJavaType result = (KeYJavaType) sort2KJTCache.get(sort);
         if(result==null && sort instanceof ArraySort){
             result = getKeYJavaType(sort.name().toString());
         }
         return result;
     }

    /** returns the KeYJavaType of the expression if it can be
     * determined else null is returned
     */
    public KeYJavaType getPrimitiveKeYJavaType(Expression e) {
        return getTypeConverter().getKeYJavaType(e);
    }

    /**
     * returns all ObjectSorts of the underlying Java model
     * @return a namespace containing the object sorts
     */
    public Namespace getObjectSorts() {
        Iterator it = kpmi.allObjectSorts().iterator();
        Namespace ns = new Namespace();
        while (it.hasNext()) {       
            ns.add((Named)it.next());            
        }
        return ns;
    }    

    /**
     * returns the KeYJavaType belonging to the given Type t
     */
    public KeYJavaType getKeYJavaType(Type t) {
        if (t instanceof PrimitiveType) {
	    return getTypeConverter().getKeYJavaType(t);
        } else {
	    if(type2KJTCache == null){
		type2KJTCache = new HashMap<Type, KeYJavaType>();
		final Iterator it = (kpmi.allElements()).iterator();
		while (it.hasNext()) {
		    Object o = it.next();
		    if (o instanceof KeYJavaType) {
		        final KeYJavaType oKJT = (KeYJavaType)o;
			type2KJTCache.put(oKJT.getJavaType(), oKJT);
		    }
		}
	    }
	    return (KeYJavaType) type2KJTCache.get(t);
	}
    }

    /**
     * returns all methods from the given Type
     */
    public ListOfMethod getAllMethods(KeYJavaType kjt) {
        return kpmi.getAllMethods(kjt);
    }

    /**
     * returns all locally declared methods from the given Type
     */
    public ListOfMethod getMethods(KeYJavaType kjt) {
        return kpmi.getMethods(kjt);
    }

    /**
     * returns all methods from the given Type as ProgramMethods
     */
    public ListOfProgramMethod getAllProgramMethods(KeYJavaType kjt) {
        return kpmi.getAllProgramMethods(kjt);
    }
    
    /**
     * returns all methods declared in the given Type as ProgramMethods
     */
    public ListOfProgramMethod getAllProgramMethodsLocallyDeclared(KeYJavaType kjt) {        
        return kpmi.getAllProgramMethodsLocallyDeclared(kjt);
    }

    /**
     * returns the program methods defined in the given KeYJavaType with name
     * m and the list of types as signature of the method 
     * @param classType the KeYJavaType of the class where to look for the 
     *  method 
     * @param methodName the name of the method
     * @param signature a ListOfType with the arguments types 
     * @param context the KeYJavaType of the class context from <em>where</em>
     *  the method is called 
     * @return a matching program method 
     */
    public ProgramMethod getProgramMethod(KeYJavaType classType, 
            String methodName,
            ListOfType signature,
            KeYJavaType context) {
        return kpmi.getProgramMethod(classType, methodName, signature, context);
    }

    /**
     * returns the program methods defined in the given KeYJavaType with name
     * m and the list of types as signature of the method
     * @param ct the KeYJavaType of the class where to look for the 
     *  method 
     * @param methodName the name of the method
     * @param signature a ListOfKeYJavaType with the arguments types 
     * @param context the KeYJavaType of the class context from <em>where</em>
     *  the method is called 
     * @return a matching program method 
     */
    public ProgramMethod getProgramMethod(KeYJavaType ct, String methodName,
					  ListOfKeYJavaType signature,
					  KeYJavaType context) {
        return kpmi.getProgramMethod(ct, methodName, signature, context);
    }


    public Term getProgramMethodTerm(Term prefix, String methodName, 
				     Term[] args,
				     String className) {
	ListOfKeYJavaType sig = SLListOfKeYJavaType.EMPTY_LIST;
	Term[] subs = new Term[args.length+1];
	subs[0] = prefix;
	for (int i = 1; i<subs.length; i++) {
              Term t = args[i-1];             
              sig=sig.append(getServices().getTypeConverter()
			     .getKeYJavaType(t));
              subs[i] = t;
	}
	className = translateArrayType(className);
	KeYJavaType clType = getKeYJavaTypeByClassName(className);
	ProgramMethod pm   = getProgramMethod(clType, methodName, sig, clType);
	if (pm==null) {
	    throw new IllegalArgumentException("Program method "+methodName
					       +" in "+className+" not found.");
	}
	if (pm.isStatic()) {
	    Term[] newSubs = new Term[subs.length-1];
	    System.arraycopy(subs,1,newSubs,0,newSubs.length);
	    subs=newSubs;
	}
	if (pm.getKeYJavaType()==null) {
	    throw new IllegalArgumentException("Program method "+methodName
					       +" in "+className+" must have"
					       +" a non-void type.");
	}
	return TermFactory.DEFAULT.createFunctionTerm(pm, subs);
    }


    /**
     * returns all direct supertypes (local declared types in extends and
     * implements) if extends is not given explict java.lang.Object is added
     * (it is not added for interfaces)
     */
    public ListOfKeYJavaType getDirectSuperTypes(KeYJavaType type) {
        final ClassType javaType = (ClassType) type.getJavaType();

        ListOfKeYJavaType localSupertypes = javaType.getSupertypes();
     
        if (!javaType.isInterface()) {
            final IteratorOfKeYJavaType it = localSupertypes.iterator();
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

	final ListOfKeYJavaType localSupertypes = javaType.getSupertypes();
	final IteratorOfKeYJavaType it = localSupertypes.iterator();
	while (result == null && it.hasNext()) {
	    final KeYJavaType keYType = it.next();
	    if (!((ClassType)keYType.getJavaType()).isInterface()) {
		result = keYType;
	    }
	}
	
	if(result == null && ((ClassDeclaration) javaType).isAnonymousClass()){
	    IteratorOfSort sit = type.getSort().extendsSorts().iterator();
	    while(sit.hasNext()){
	        Sort s = sit.next();
	        if(!((ClassType) getKeYJavaType(s).getJavaType()).isInterface()){
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
    public ProgramMethod getProgramMethod
	(KeYJavaType classType, String methodName, ProgramVariable[] args,
	        KeYJavaType context){
        ListOfType types = SLListOfType.EMPTY_LIST;
        for (int i = args.length - 1; i>=0; i--) {
            types = types.prepend(args[i].getKeYJavaType());
        }
        return getProgramMethod(classType, methodName, types, context);
    }

    /** gets an array of expression and returns a list of types */
    private ListOfKeYJavaType getKeYJavaTypes(ArrayOfExpression args) {
	ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST; 
	if (args != null) {
	    for (int i = args.size()-1; i >= 0 ; i--) {
		final Expression argument = args.getExpression(i);
		result = result.prepend
		    (getTypeConverter().getKeYJavaType(argument));
	    }
	}
	return result;
    }


    /**
     * retrieves the signature according to the given expressions
     * @param arguments ArrayOfExpression of which we try to construct a
     * signature 
     * @return the signature 
     */
    public ListOfKeYJavaType createSignature(ArrayOfExpression arguments) {
	return getKeYJavaTypes(arguments);    
    }

    /**
     * retrieves all attributes locally declared in class <tt>cl</tt> 
     * (inclusive the implicit attributes)
     * The returned list is in source code order. 
     * @param classDecl the ClassDeclaration whose attributes shall be collected
     * @return all attributes declared in class <tt>cl</tt> 
     */
    public ListOfField getAllFields(ClassDeclaration classDecl) {
	return filterLocalDeclaredFields(classDecl, Filter.TRUE);
    }

    /**
     * retrieves all implicit attributes locally declared in the given class 
     * The returned list is in source code order.
     * @param cl the ClassDeclaration where to look for the implicit
     * attributes 
     * @return all implicit attributes declared in <tt>cl</tt>
     */
    public ListOfField getImplicitFields(ClassDeclaration cl) {
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
    private ListOfField filterLocalDeclaredFields(ClassDeclaration classDecl,
            Filter filter) {
        ListOfField fields = SLListOfField.EMPTY_LIST;
        final ArrayOfMemberDeclaration members = classDecl.getMembers();
        for (int i = members.size()-1; i>=0; i--) {
            final MemberDeclaration member = members.getMemberDeclaration(i);
            if (member instanceof FieldDeclaration) {
        	final ArrayOfFieldSpecification specs = 
        	    ((FieldDeclaration)member).getFieldSpecifications();
        	for (int j = specs.size()-1; j>=0; j--) {
        	    final FieldSpecification fieldSpec = specs.getFieldSpecification(j);
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
        // if we are here everything is fine nad wen can add the
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
     * returns a term representing 'null' in logic
     */
    public Term getNullTerm() {
        return getTypeConverter().convertToLogicElement(NullLiteral.NULL);
    }


    /**
     * retrieves a field with the given name out of the list
     * @param programName a String with the name of the field to be looked for
     * @param fields the ListOfField where we have to look for the field
     * @return the program variable of the given name or null if not
     * found
     */
    private final ProgramVariable find(String programName, 
                                       ListOfField fields) {
	IteratorOfField it = fields.iterator();
	while (it.hasNext()) {
	    Field field = it.next();
	    if (programName.equals(field.getProgramName())) {
		return (ProgramVariable)
		    ((FieldSpecification)field).getProgramVariable();
	    }
	}
	return null;
    }

    /**
     * extracts all fields out of fielddeclaration
     * @param field the FieldDeclaration of which the field
     * specifications have to be extracted
     * @return a ListOfField the includes all field specifications found
     * int the field declaration of the given list
     */
    private final ListOfField getFields(FieldDeclaration field) {
	ListOfField result = SLListOfField.EMPTY_LIST;
	final ArrayOfFieldSpecification spec = field.getFieldSpecifications();
	for (int i = spec.size()-1; i>=0; i--) {
	    result = result.prepend(spec.getFieldSpecification(i));
	} 
	return result;
    }

    /**
     * extracts all field specifications out of the given
     * list. Therefore it descends into field declarations.
     * @param list the ArrayOfMemberDeclaration with the members of a
     * type declaration
     * @return a ListOfField the includes all field specifications found
     * int the field declaration of the given list
     */
    private ListOfField getFields(ArrayOfMemberDeclaration list) {
	ListOfField result = SLListOfField.EMPTY_LIST;
	for (int i = list.size()-1; i >= 0; i--) {
	    final MemberDeclaration pe = list.getMemberDeclaration(i);
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
     */
    public ProgramVariable getAttribute(String programName, 
            String qualifiedClassName) {
	if (qualifiedClassName == null || qualifiedClassName.length() == 0) {
            throw new IllegalArgumentException("Missing qualified classname");
        }
        KeYJavaType kjt=null;
        try{
            kjt = getKeYJavaTypeByClassName(qualifiedClassName);
        }catch(Exception e){
            if(qualifiedClassName.endsWith("]")){
                readJavaBlock("{" + qualifiedClassName + " k;}");
                kjt = getKeYJavaType(qualifiedClassName);
            }
        }
        return getAttribute(programName, 
			    getKeYJavaTypeByClassName(qualifiedClassName));
    }

    
    /**
     * returns the program variable representing the attribute of the given 
     * name declared locally in class <tt>classType</tt>
     * @return the attribute of the given name declared in <tt>classType</tt> 
     */
    public ProgramVariable getAttribute(final String name,
					KeYJavaType classType) {       
	if (classType.getJavaType() instanceof ArrayDeclaration) {
            ProgramVariable res = find(name, getFields
                        (((ArrayDeclaration)classType.
                                getJavaType()).getMembers()));
            if (res==null) {               
		return getAttribute(name, getJavaLangObject());
	    } 
            return res;
	} else {
	    final ListOfField list   = kpmi.getAllFieldsLocallyDeclaredIn(classType);
	    final IteratorOfField it = list.iterator();	   
            while (it.hasNext()) {
		final Field f = it.next();
		if (f!=null && (f.getName().equals(name) || 
		                f.getProgramName().equals(name))) {
		    return (ProgramVariable)((VariableSpecification)f).
                    getProgramVariable();
		}
	    }
	}
	return null;
    }

    public int getSizeInBytes(KeYJavaType classType){
	int size = 8;
	if(classType.toString().indexOf("[")!=-1) return 0;
        size += getSizeInBytesRec(classType);
        if(size % 8 == 0){
            return size;
        }else{
            return (size/8+1)*8;
        }
    }
    
    private int getSizeInBytesRec(KeYJavaType classType){
        if(classType == getJavaLangObject() || classType == null) return 0;
        int size = 0;
        ListOfField l = kpmi.getAllFieldsLocallyDeclaredIn(classType);
        size += sizeInBytes(l);
        size += getSizeInBytesRec(getSuperclass(classType));
        return size;
    }
    
    private int sizeInBytes(ListOfField l){
        int size = 0;
        while(!l.isEmpty()){
            if(l.head() instanceof ImplicitFieldSpecification){
                l = l.tail();
                continue;
            }
            String fType = l.head().getProgramVariable().getKeYJavaType().
                getSort().toString();
            l = l.tail();
            if(fType.equals("jbyte") || fType.equals("boolean")){
                size += 1;
            }else if(fType.equals("jshort") || fType.equals("jchar")){
                size += 2;
            }else if(fType.equals("jlong")){
                size += 8;
            }else{
                size += 4;
            }
        }
        return size;
    }

    /**
     * returns an attribute named <tt>attributeName</tt> declared locally 
     * in object type <tt>s</tt>    
     */
    public ProgramVariable getAttribute(String attributeName, ObjectSort s) {
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
    public ListOfProgramVariable getAllAttributes(String programName, 
                                                  KeYJavaType type) {
                                

        ListOfProgramVariable result = 
            SLListOfProgramVariable.EMPTY_LIST;      
        
	if (!(type.getSort() instanceof ObjectSort)) {
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
        ListOfKeYJavaType hierarchie = kpmi.getAllSubtypes(type);                
        assert !hierarchie.contains(type);
        
        hierarchie = hierarchie.prepend(kpmi.getAllSupertypes(type));        
        assert hierarchie.head() == type;
        
        
        final IteratorOfKeYJavaType it = hierarchie.iterator();
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
    
    
    private void fillCommonTypesCache() {
        if (commonTypesCacheValid) return;
        final String[] fullNames = {"java.lang.Object", 
                "java.lang.Cloneable", "java.io.Serializable",
                "javax.realtime.ScopedMemory"};
        
        for (int i = 0; i<fullNames.length; i++) {
            commonTypes[i] = getKeYJavaTypeByClassName(fullNames[i]);            
        }
        commonTypesCacheValid = true;
    }

    /**
     * returns the KeYJavaType for class <tt>java.lang.Object</tt>
     */
    public KeYJavaType getJavaLangObject() {
        if (commonTypes[0] == null) {
            commonTypes[0] = getKeYJavaTypeByClassName("java.lang.Object");
        }
        return commonTypes[0];
    }


    /**
     * returns the KeYJavaType for class java.lang.Clonable
     */
    public KeYJavaType getJavaLangCloneable() {
        if (commonTypes[1] == null) {
            commonTypes[1] = getKeYJavaTypeByClassName("java.lang.Cloneable");
        }
        return commonTypes[1];
    }

    /**
     * returns the KeYJavaType for class <tt>java.io.Serializable</tt>
     */
    public KeYJavaType getJavaIoSerializable() {
        if (commonTypes[2] == null) {
            commonTypes[2] = getKeYJavaTypeByClassName("java.io.Serializable");
        }
        return commonTypes[2];
    }
    
    /**
     * returns the KeYJavaType for class <tt>java.realtime.ScopedMemory</tt>
     */
    public KeYJavaType getJavaxRealtimeScopedMemory() {
        if (commonTypes[3] == null) {
            commonTypes[3] = getKeYJavaTypeByClassName("javax.realtime.ScopedMemory");
        }
        return commonTypes[3];
    }


    
    /**
     * returns the KeYJavaType for class java.lang.Object
     */
    public Sort getJavaLangObjectAsSort() {
	return getJavaLangObject().getSort();	
    }

    /**
     * returns the KeYJavaType for class java.lang.Cloneable
     */
    public Sort getJavaLangCloneableAsSort() {   
        return getJavaLangCloneable().getSort();        
    }

    /**
     * returns the KeYJavaType for class java.io.Serializable
     */
    public Sort getJavaIoSerializableAsSort() {   
        return getJavaIoSerializable().getSort();        
    }
    
    /**
     * tests if sort represents java.lang.Object, java.lang.Cloneable or 
     * java.io.Serializable
     */
    public boolean isAJavaCommonSort(Sort sort) {
        if (!commonTypesCacheValid) { 
            fillCommonTypesCache();
        }
        for (int i = 0; i<commonTypes.length; i++) {
            if (commonTypes[i].getSort() == sort) {
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
	    nullType = getKeYJavaTypeByClassName("null");
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
                getKeYJavaTypeByClassName(DEFAULT_EXECUTION_CONTEXT_CLASS);                     
            defaultExecutionContext = 
                new ExecutionContext(new TypeRef(kjt), getDefaultMemoryArea(),
                        null);
        }
        return defaultExecutionContext;
    }
    
    public LocationVariable getDefaultMemoryArea(){
        if(defaultMemoryArea==null){
            // ensure that default classes are available
            if (!kpmi.rec2key().parsedSpecial()) {
                readJava("{}");                
            }
            defaultMemoryArea = (LocationVariable) services.getNamespaces().
                programVariables().lookup(new Name("initialMemoryArea"));
            KeYJavaType kjt = getTypeByClassName("javax.realtime.ScopedMemory");
            if(defaultMemoryArea == null){
                defaultMemoryArea = 
                    new LocationVariable(new ProgramElementName("initialMemoryArea"),
                            kjt);
                services.getNamespaces().programVariables().add(defaultMemoryArea);
            }
        }
        return defaultMemoryArea;
    }
    
    public LocationVariable getImmortalMemoryArea(){
        if(immortalMemoryArea==null){
            // ensure that default classes are available
            if (!kpmi.rec2key().parsedSpecial()) {
                readJava("{}");                
            }
            immortalMemoryArea = (LocationVariable) services.getNamespaces().
                programVariables().lookup(new Name("immortalMemoryArea"));
            KeYJavaType kjt = getTypeByClassName("javax.realtime.ScopedMemory");
            if(immortalMemoryArea == null){
                immortalMemoryArea = 
                    new LocationVariable(new ProgramElementName("immortalMemoryArea"),
                            kjt);
                services.getNamespaces().programVariables().add(immortalMemoryArea);
            }
        }
        return immortalMemoryArea;
    }
    
    
    /**
     * returns a term representing the null constant in logic
     */
    public Term getNullConst() {
	if (nullConst==null) {
	    nullConst=TermFactory.DEFAULT.createFunctionTerm(Op.NULL);
	}
	return nullConst;
    }
    
    /**
     * returns all proper subtypes of a given type
     * @param type the KeYJavaType whose subtypes are returned
     * @return list of all subtypes
     */
    public ListOfKeYJavaType getAllSubtypes(KeYJavaType type) {
        return kpmi.getAllSubtypes(type);
    }
    
    /**
     * returns all supertypes of a given type
     * @param type the KeYJavaType whose supertypes are returned
     * @return list of all supertypes
     */
    public ListOfKeYJavaType getAllSupertypes(KeYJavaType type) {
        if (type.getJavaType() instanceof ArrayType) {
            ListOfKeYJavaType arraySupertypes = SLListOfKeYJavaType.EMPTY_LIST;
            final IteratorOfSort it = 
                ((ArraySort)type.getSort()).extendsSorts().iterator();
            while (it.hasNext()) {
                arraySupertypes.append(getKeYJavaType(it.next()));
            }
            return arraySupertypes;
        }
        return kpmi.getAllSupertypes(type);
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
    
    public void setJavaSourcePath(String path) {
        javaSourcePath = path;
    }
    
    public String getJavaSourcePath() {
        return javaSourcePath;
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
    public ListOfKeYJavaType getCommonSubtypes(KeYJavaType k1, KeYJavaType k2) {        
        final CacheKey ck = new CacheKey(k1, k2);
        ListOfKeYJavaType result = (ListOfKeYJavaType)commonSubtypeCache.get(ck);
        
        if (result != null) {
            return result;
        } 
         
        result = SLListOfKeYJavaType.EMPTY_LIST;
        
        if (k1.getSort().extendsTrans(k2.getSort())) { 
            result = getAllSubtypes(k1).prepend(k1);
        } else if (k2.getSort().extendsTrans(k1.getSort())) { 
            result = getAllSubtypes(k2).prepend(k2);
        } else {
            final ListOfKeYJavaType l1 = getAllSubtypes(k1);                
            final ListOfKeYJavaType l2 = getAllSubtypes(k2);

            final IteratorOfKeYJavaType it = l1.iterator();

            while (it.hasNext()) {
                final KeYJavaType next = it.next();
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
                getVariableSpecification(0).getProgramVariable();
            assert "length".equals(length.name().toString()) : "Wrong array length";
        }
        
        return length;
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

}
