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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import recoder.abstraction.ClassType;
import recoder.abstraction.Constructor;
import recoder.java.CompilationUnit;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Method;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYExceptionHandler;

public class KeYProgModelInfo{


    private Services services;
    private KeYCrossReferenceServiceConfiguration sc = null;
    private KeYRecoderMapping mapping;
    private TypeConverter typeConverter;
    private HashMap<KeYJavaType, HashMap<String, IProgramMethod>> implicits =
        new LinkedHashMap<KeYJavaType, HashMap<String, IProgramMethod>>();
    private KeYExceptionHandler exceptionHandler = null;

    public KeYProgModelInfo(Services services, TypeConverter typeConverter,
            KeYExceptionHandler keh){
 	this(services, new KeYCrossReferenceServiceConfiguration(keh),
	     new KeYRecoderMapping(), typeConverter);
	exceptionHandler = keh;
    }

    KeYProgModelInfo(Services services, KeYCrossReferenceServiceConfiguration crsc,
		     KeYRecoderMapping krm, TypeConverter typeConverter) {
        this.services = services;
	 sc = crsc;
	 this.typeConverter = typeConverter;
	 this.mapping       = krm;
     }


    public KeYRecoderMapping rec2key() {
	return mapping;
    }

    public KeYCrossReferenceServiceConfiguration getServConf() {
	return sc;
    }

    public KeYExceptionHandler getExceptionHandler(){
	return exceptionHandler;
    }

    /**
     * Returns all KeY-elements mapped by Recoder2KeY object of this
     * KeYProgModelInfo.
     * @return a Set object containing the KeY-elements.
     */

    public Set<?> allElements(){
        return rec2key().elemsKeY();
    }

    private List<recoder.abstraction.Method> getAllRecoderMethods(KeYJavaType kjt){
	if (kjt.getJavaType() instanceof TypeDeclaration) {
	    Object o = rec2key().toRecoder(kjt);
	    if (o instanceof recoder.abstraction.ClassType) {
		recoder.abstraction.ClassType rtd
		    = (recoder.abstraction.ClassType) o;
		return rtd.getAllMethods();
	    }
	}
	return new ArrayList<recoder.abstraction.Method>();
    }


    /**Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     * @return the list of visible methods of this type and its supertypes.
     */

    public ImmutableList<Method> getAllMethods(KeYJavaType kjt) {
        List<recoder.abstraction.Method> rmethods=getAllRecoderMethods(kjt);
        ImmutableList<Method> result = ImmutableSLList.<Method>nil();
        for (int i=rmethods.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rmethods.get(i);
            Method m=
		((IProgramMethod)rec2key().toKeY(rm)).getMethodDeclaration();
            result=result.prepend(m);
        }
        return result;
    }


    /**Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     * @return the list of visible methods of this type and its supertypes.
     */

    public ImmutableList<IProgramMethod> getAllProgramMethods(KeYJavaType kjt) {
        List<recoder.abstraction.Method> rmethods=getAllRecoderMethods(kjt);
        ImmutableList<IProgramMethod> result = ImmutableSLList.<IProgramMethod>nil();
        for (int i=rmethods.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rmethods.get(i);
            IProgramMethod m=(IProgramMethod)rec2key().toKeY(rm);
	    if (m!=null) {
		result=result.prepend(m);
	    }
        }
        return result;
    }

    private List<recoder.abstraction.Type> getRecoderTypes(ImmutableList<? extends Type> types) {
        if (types==null) {
            return null;
        }
        final ArrayList<recoder.abstraction.Type> tl
            = new ArrayList<recoder.abstraction.Type>(types.size());
        for (final Type n : types) {
            tl.add( (recoder.abstraction.Type) rec2key().toRecoder(n));
        }
        return tl;
    }


    public KeYJavaType resolveType(String shortName, KeYJavaType context) {
        recoder.abstraction.ClassType result = null;

        recoder.abstraction.Type rt
        = (recoder.abstraction.Type) rec2key().toRecoder(context);


       if (rt instanceof recoder.java.declaration.ClassDeclaration) {

           // check for inner types
           result = searchType(shortName, ((recoder.java.declaration.ClassDeclaration) rt).getTypes());

           if (result != null) {
               return (KeYJavaType) rec2key().toKeY(result);
           }

           // check for imported types
           recoder.java.NonTerminalProgramElement rct = (recoder.java.NonTerminalProgramElement) rt;
           recoder.java.CompilationUnit cunit = null;
           while (!(rct.getASTParent() instanceof recoder.java.CompilationUnit)) {
               rct = rct.getASTParent();
           }

           cunit = (CompilationUnit) rct.getASTParent();

           for (recoder.java.Import i : cunit.getImports()) {
               final List<? extends recoder.abstraction.ClassType> types;
               if (i.getPackageReference() != null) {
                  types = sc.getCrossReferenceSourceInfo().getPackage(i.getPackageReference()).getTypes();
               } else {
                   if (i.isMultiImport()) {
                       recoder.abstraction.ClassType type = (recoder.abstraction.ClassType)sc.getCrossReferenceSourceInfo().getType(i.getTypeReference());
                       types = type.getTypes();
                   } else {
                       types = new LinkedList<recoder.abstraction.ClassType>();
                       ((LinkedList<recoder.abstraction.ClassType>)types).add((recoder.abstraction.ClassType)sc.getCrossReferenceSourceInfo().getType(i.getTypeReference()));
                   }
               }
               result = searchType(shortName, types);
               if (result != null) {
                   return (KeYJavaType) rec2key().toKeY(result);
               }

           }
       }
       return null;

    }

    private recoder.abstraction.ClassType searchType(String shortName,
            final List<? extends ClassType> types) {
        for (recoder.abstraction.ClassType type : types) {
            if (type.getName().equals(shortName)) {
                return type;
            }
        }
        return null;
    }

    /**
     * Returns the full name of a KeYJavaType t.
     * @return the full name of t as a String.
     */

    public String getFullName(KeYJavaType t) {
        recoder.abstraction.Type rt
            = (recoder.abstraction.Type) rec2key().toRecoder(t);
        return rt.getFullName();
    }

    public recoder.abstraction.Type getType(TypeReference tr) {
        recoder.abstraction.Type result;
        if (tr instanceof TypeRef) {
            result = (recoder.abstraction.Type)
            rec2key().toRecoder(((TypeRef)tr).getKeYJavaType());
            return result;
        }
        result=getServConf().getSourceInfo().getType
            ((recoder.java.reference.TypeReference)rec2key().toRecoder(tr));
        return result;
    }


    public boolean isFinal(KeYJavaType kjt) {
        final recoder.abstraction.Type recoderType =
                (recoder.abstraction.Type) rec2key().toRecoder(kjt);
        if (recoderType instanceof recoder.java.declaration.TypeDeclaration) {
            final recoder.java.declaration.TypeDeclaration td =
                    (recoder.java.declaration.TypeDeclaration) recoderType;
            return td.isFinal();
        } else // array or primitive type
            return false;
    }


    /**
     * Checks whether subType is a subtype of superType or not.
     * @returns true if subType is subtype of superType,
     * false in the other case.
     */

    public boolean isSubtype(KeYJavaType subType, KeYJavaType superType) {
	return isSubtype((recoder.abstraction.Type)rec2key().toRecoder(subType),
			 (recoder.abstraction.Type)rec2key().toRecoder(superType));
    }

    private boolean isSubtype(recoder.abstraction.Type subType,
			      recoder.abstraction.Type superType) {
	if (subType instanceof recoder.abstraction.ClassType &&
	    superType instanceof recoder.abstraction.ClassType) {
	    return isSubtype((recoder.abstraction.ClassType)subType,
			     (recoder.abstraction.ClassType)superType);
	} else if (superType instanceof recoder.abstraction.ArrayType &&
		   subType instanceof recoder.abstraction.ArrayType) {
	    return isAssignmentCompatible((recoder.abstraction.ArrayType)subType,
					  (recoder.abstraction.ArrayType)superType);
	}else if(subType instanceof recoder.abstraction.ArrayType &&
		 superType instanceof recoder.abstraction.ClassType){
	    return "java.lang.Object".equals(superType.getFullName())
		|| "Object".equals(superType.getName());
	}
	// should not occur
	throw new RuntimeException("Method isSubtype in class KeYProgModelInfo "+
				   "currently only supports two class types or two "+
				   "array type but no mixture!");
    }

    private boolean isSubtype(recoder.abstraction.ClassType classSubType,
            recoder.abstraction.ClassType classType) {
        boolean isSub =  getServConf().getSourceInfo().
        isSubtype(classSubType, classType);
        if (!isSub) {
            boolean result= getServConf().getByteCodeInfo().
            isSubtype(classSubType, classType);
            return result;
        } else {
            return true;
        }
    }

    /**
     * create a recoder package reference out of a IDENT (DOT IDENT)+
     * String
     */
    private recoder.java.reference.PackageReference
	createPackageReference(String pkgName) {
	final int lastDot = pkgName.lastIndexOf('.');
	if (lastDot != -1) {
	    return new recoder.java.reference.PackageReference
		(createPackageReference
		 (pkgName.substring(0,lastDot)),
		  new recoder.java.Identifier(pkgName.substring(lastDot+1)));
	}
	return new recoder.java.reference.PackageReference
	    (new recoder.java.Identifier(pkgName));
    }

    /**
     * checks if name refers to a package
     * @param name a String with the name to be checked
     * @return true iff name refers to a package
     */
    public boolean isPackage(String name) {
	return ((recoder.service.DefaultNameInfo)sc.getNameInfo()).isPackage(name);
    }

    /**
     * checks whether subType is assignment compatible to type according
     * to the rules defined in the java language specification
     */
    private boolean isAssignmentCompatible(recoder.abstraction.ArrayType subType,
					   recoder.abstraction.ArrayType type) {
	recoder.abstraction.Type bt1 = subType.getBaseType();
	recoder.abstraction.Type bt2 = type.getBaseType();
	if (bt1 instanceof recoder.abstraction.PrimitiveType &&
	    bt2 instanceof recoder.abstraction.PrimitiveType) {
	    return bt1.getFullName().equals(bt2.getFullName());
	}
	if (bt1 instanceof recoder.abstraction.ClassType &&
	    bt2 instanceof recoder.abstraction.ClassType)
	    return isSubtype((recoder.abstraction.ClassType)bt1,
			     (recoder.abstraction.ClassType)bt2);
	if (bt1 instanceof recoder.abstraction.ArrayType &&
	    bt2 instanceof recoder.abstraction.ArrayType)
	    return isAssignmentCompatible((recoder.abstraction.ArrayType)bt1,
					  (recoder.abstraction.ArrayType)bt2);
 	if (bt1 instanceof recoder.abstraction.ClassType &&
	    bt2 instanceof recoder.abstraction.ArrayType)
	    return false;
	if (bt1 instanceof recoder.abstraction.ArrayType &&
	    bt2 instanceof recoder.abstraction.ClassType) {
	    if (((recoder.abstraction.ClassType)bt2).isInterface()) {
		return ((recoder.abstraction.ClassType)bt2).
                    getFullName().equals("java.lang.Cloneable") ||
                    ((recoder.abstraction.ClassType)bt2).
                    getFullName().equals("java.lang.Serializable")
                    ;
	    } else {
		return ((recoder.abstraction.ClassType)bt2).
		    getFullName().equals("java.lang.Object");
	    }
	}
	return false;
    }

    private List<recoder.abstraction.Method> getRecoderMethods(KeYJavaType kjt){
        if (kjt.getJavaType() instanceof TypeDeclaration) {
            Object o = rec2key().toRecoder(kjt);
            if (o instanceof recoder.abstraction.ClassType) {
                recoder.abstraction.ClassType rct
                    = (recoder.abstraction.ClassType) o;
                return rct.getProgramModelInfo().getMethods(rct);
            }
        }
        return new ArrayList<recoder.abstraction.Method>();
    }

    private List<? extends recoder.abstraction.Constructor> getRecoderConstructors(KeYJavaType ct){
        recoder.abstraction.ClassType rct
            = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        return rct.getProgramModelInfo().getConstructors(rct);
    }

    private List<recoder.abstraction.Method> getRecoderMethods
	(KeYJavaType ct, String m, ImmutableList<? extends Type> signature, KeYJavaType context){
        recoder.abstraction.ClassType rct
            = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        recoder.abstraction.ClassType rcontext
            = (recoder.abstraction.ClassType) rec2key().toRecoder(context);

        return rct.getProgramModelInfo().getMethods(rct, m,
						    getRecoderTypes(signature),
						    null,  // no generic type variables yet
						    rcontext);
    }


    private List<? extends recoder.abstraction.Constructor> getRecoderConstructors
	(KeYJavaType ct, ImmutableList<KeYJavaType> signature){
        recoder.abstraction.ClassType rct
            = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
	List<? extends recoder.abstraction.Constructor> res
		= rct.getProgramModelInfo().getConstructors
	    (rct, getRecoderTypes(signature));
	return res;
    }


    /**
     * Returns the list of most specific methods with the given
     * name that are defined in the given type or in a supertype
     * where they are visible for the given type, and have a signature
     * that is compatible to the given one. If used to resolve a
     * method call, the result should be defined and unambiguous.
     * @param ct the class type to get methods from.
     * @param m the name of the methods in question.
     * @param signature the statical type signature of a callee.
     */

    public ImmutableList<Method> getMethods(KeYJavaType ct, String m,
				   ImmutableList<Type> signature, KeYJavaType context){
        List<recoder.abstraction.Method> rml =
	    getRecoderMethods(ct, m, signature, context);
        ImmutableList<Method> result = ImmutableSLList.<Method>nil();
        for (int i=rml.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rml.get(i);
            Method method=(Method)rec2key().toKeY(rm);
            result=result.prepend(method);
        }
        return result;
    }


	/**
	 * Returns the methods locally defined within the given
	 * class type. If the type is represented in source code,
	 * the returned list matches the syntactic order.
	 * @param ct a class type.
	 */

    public ImmutableList<Method> getMethods(KeYJavaType ct){
        List<recoder.abstraction.Method> rml = getRecoderMethods(ct);
        ImmutableList<Method> result = ImmutableSLList.<Method>nil();
        for (int i=rml.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rml.get(i);
	    if(!(rm instanceof recoder.bytecode.MethodInfo)){
		Method m = ((IProgramMethod) rec2key().toKeY(rm)).
		    getMethodDeclaration();
		result=result.prepend(m);
	    }
        }
        return result;
    }

	/**
	 * Returns the IProgramMethods locally defined within the given
	 * class type. If the type is represented in source code,
	 * the returned list matches the syntactic order.
	 * @param ct a class type.
	 */
    public ImmutableList<IProgramMethod> getAllProgramMethodsLocallyDeclared(KeYJavaType ct){
        List<recoder.abstraction.Method> rml = getRecoderMethods(ct);
        ImmutableList<IProgramMethod> result = ImmutableSLList.<IProgramMethod>nil();
        for (int i=rml.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rml.get(i);
	    if(!(rm instanceof recoder.bytecode.MethodInfo)){
		result = result.prepend((IProgramMethod) rec2key().toKeY(rm));
	    }
        }
        return result;
    }

	/**
	 * Returns the constructors locally defined within the given
	 * class type. If the type is represented in source code,
	 * the returned list matches the syntactic order.
	 * @param ct a class type.
	 */

    public ImmutableList<IProgramMethod> getConstructors(KeYJavaType ct){
        List<? extends Constructor> rcl = getRecoderConstructors(ct);
        ImmutableList<IProgramMethod> result = ImmutableSLList.<IProgramMethod>nil();
        for (int i=rcl.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rcl.get(i);
	    IProgramMethod m=(IProgramMethod) rec2key().toKeY(rm);
	    if(m != null){
		result=result.prepend(m);
	    }
        }
        return result;
    }

    /**
     * retrieves the most specific constructor declared in the given type with
     * respect to the given signature
     * @param ct the KeYJavyType where to look for the constructor
     * @param signature IList<KeYJavaType> representing the signature of the constructor
     * @return the most specific constructor declared in the given type
     */
    public IProgramMethod getConstructor(KeYJavaType ct,
				       ImmutableList<KeYJavaType> signature) {
        List<? extends recoder.abstraction.Constructor> constructors =
            getRecoderConstructors(ct, signature);
        if (constructors.size()==1) {
            return (IProgramMethod) rec2key().toKeY(constructors.get(0));
        }
        if (constructors.size()==0) {
            Debug.out("javainfo: Constructor not found: ",ct);
            return null;
        }
        Debug.fail();
        return null;
    }

    /**
     * retrieves implicit methods
     */
    private IProgramMethod getImplicitMethod(KeYJavaType ct, String name) {
	final HashMap<String, IProgramMethod> m = implicits.get(ct);
	if (m!=null) {
	    final IProgramMethod pm = m.get(name);
	    if (pm!=null) {
		return pm;
	    }
	}
 	TypeDeclaration cd = (TypeDeclaration)ct.getJavaType();
 	ImmutableArray<MemberDeclaration> members = cd.getMembers();
 	for (int i = 0; i<members.size(); i++) {
 	    final MemberDeclaration member = members.get(i);
 	    if (member instanceof IProgramMethod &&
 		((IProgramMethod)member).getMethodDeclaration().getName().equals(name)) {
 		return (IProgramMethod)member;
 	    }
 	}
 	Debug.out("keyprogmodelinfo: implicit method %1 not found in %2 (%1, %2) ",
 		  name, ct);
 	return null;
    }


    /**
     * Returns the IProgramMethods with the given name that is defined
     * in the given type or in a supertype where it is visible for the
     * given type, and has a signature that is compatible to the given one.
     * @param ct the class type to get methods from.
     * @param m the name of the methods in question.
     * @param signature the statical type signature of a callee.
     * @return the IProgramMethods, if one is found,
     * null if none or more than one IProgramMethod is found (in this case
     * a debug output is written to console).
     */
    public IProgramMethod getProgramMethod(KeYJavaType ct, String m,
					  ImmutableList<? extends Type> signature,
					  KeYJavaType context) {
	if (ct.getJavaType() instanceof ArrayType ||
	    context.getJavaType() instanceof ArrayType) {
            return getImplicitMethod(ct, m);
	}

	List<recoder.abstraction.Method> methodlist =
	        getRecoderMethods(ct, m, signature, context);

        if (methodlist.size()==1) {
            return (IProgramMethod) rec2key().toKeY(methodlist.get(0));
        } else if (methodlist.size()==0) {
            Debug.out("javainfo: Program Method not found: ", m);
            return null;
        } else {
	    Debug.fail();
	    return null;
	}
    }


    /**
     * returns the same fields as given in <tt>rfl</tt> and returns
     * their KeY representation
     * @param rfl the List of fields to be looked up
     * @return list with the corresponding fields as KeY datastructures
     */
    private ImmutableList<Field> asKeYFields(List<? extends recoder.abstraction.Field> rfl) {
        ImmutableList<Field> result = ImmutableSLList.<Field>nil();
        if(rfl == null){
            // this occurs for the artificial Null object at the moment
            // should it have implicit fields?
            return result;
        }
        for (int i=rfl.size()-1; i>=0; i--) {
            recoder.abstraction.Field rf = rfl.get(i);
            Field f = (Field)rec2key().toKeY(rf);
            if (f != null) {
                result = result.prepend(f);
            } else {
                Debug.out("Field has no KeY equivalent (recoder field):", rf.getFullName());
                Debug.out("This happens currently as classes only available in byte code " +
                                "are only partially converted ");
            }
        }
        return result;
    }

    /**
     * returns the fields defined within the given class type.
     * If the type is represented in source code, the returned list
     * matches the syntactic order.
     * @param ct the class type whose fields are returned
     * @return the list of field members of the given type.
     */
    public ImmutableList<Field> getAllFieldsLocallyDeclaredIn(KeYJavaType ct){
        if (ct.getJavaType() instanceof ArrayType) {
            return getVisibleArrayFields(ct);
        }
        recoder.abstraction.ClassType rct = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);

        return asKeYFields(rct.getProgramModelInfo().getFields(rct));
    }


    /**
     * returns all in <tt>ct</tt> visible fields
     * declared in <tt>ct</tt> or one of its supertypes
     * in topological order starting with the fields of
     * the given type
     *  If the type is represented in source code, the returned list
     * matches the syntactic order.
     * @param ct the class type whose fields are returned
     * @return the list of field members of the given type.
     */
    public ImmutableList<Field> getAllVisibleFields(KeYJavaType ct){
        if (ct.getJavaType() instanceof ArrayDeclaration) {
            return getVisibleArrayFields(ct);
        }

        recoder.abstraction.ClassType rct
        = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        List<recoder.abstraction.Field> rfl =
            rct.getProgramModelInfo().getAllFields(rct);

        return asKeYFields(rfl);
    }

    /**
     * returns all fields of and visible in an array field
     * @param arrayType the KeYJavaType of the array
     * @return the list of visible fields
     */
    private ImmutableList<Field> getVisibleArrayFields(KeYJavaType arrayType) {
        ImmutableList<Field> result = ImmutableSLList.<Field>nil();

        final ImmutableArray<MemberDeclaration> members =
            ((ArrayDeclaration)arrayType.getJavaType()).getMembers();

        for (int i = members.size()-1; i>=0; i--){
            final MemberDeclaration member = members.get(i);
            if (member instanceof FieldDeclaration) {
                final ImmutableArray<FieldSpecification> specs =
                    ((FieldDeclaration)member).getFieldSpecifications();
                for (int j = specs.size() - 1; j>=0; j--) {
                    result = result.prepend(specs.get(j));
                }
            }
        }

        //      fields of java.lang.Object visible in an array
        final ImmutableList<Field> javaLangObjectField =
            getAllVisibleFields((KeYJavaType)rec2key().
                                toKeY(sc.getNameInfo().getJavaLangObject()));

        for (Field aJavaLangObjectField : javaLangObjectField) {
            final Field f = aJavaLangObjectField;

            if (!((recoder.abstraction.Field)
                    rec2key().toRecoder(f)).isPrivate()) {
                result = result.append(f);
            }
        }
        return result;
    }

    /**
     * returns all proper subtypes of class <code>ct</code> (i.e. without <code>ct</code> itself)
     */
    private List<recoder.abstraction.ClassType> getAllRecoderSubtypes(KeYJavaType ct){
        return sc.getCrossReferenceSourceInfo().
            getAllSubtypes((recoder.abstraction.ClassType)rec2key().toRecoder(ct));
    }

    /**
     * returns all supertypes of the given class type with the type itself as
     * first element
     */
    private List<recoder.abstraction.ClassType> getAllRecoderSupertypes(KeYJavaType ct){
        return sc.getCrossReferenceSourceInfo().
           getAllSupertypes((recoder.abstraction.ClassType)rec2key().toRecoder(ct));
    }


    /**
     * returns a list of KeYJavaTypes representing the given recoder types in
     * the same order
     * @param rctl the ASTList<ClassType> to be converted
     * @return list of KeYJavaTypes representing the given recoder types in
     * the same order
     */
    private ImmutableList<KeYJavaType> asKeYJavaTypes(final List<recoder.abstraction.ClassType> rctl) {
        ImmutableList<KeYJavaType> result = ImmutableSLList.<KeYJavaType>nil();
        for (int i=rctl.size()-1; i>=0 ; i--){
            final recoder.abstraction.ClassType rct = rctl.get(i);
            final KeYJavaType kct = (KeYJavaType)rec2key().toKeY(rct);
	    if(kct!=null){
		result = result.prepend(kct);
	    }
        }
        return result;
    }

    /**
     * Returns all known subtypes of the given class type.
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ImmutableList<KeYJavaType> getAllSupertypes(KeYJavaType ct){
        return asKeYJavaTypes(getAllRecoderSupertypes(ct));
    }

    /**
     * Returns all proper subtypes of the given class type
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ImmutableList<KeYJavaType> getAllSubtypes(KeYJavaType ct){
        return asKeYJavaTypes(getAllRecoderSubtypes(ct));
    }

    private Recoder2KeY createRecoder2KeY(NamespaceSet nss) {
	return new Recoder2KeY(services, sc, rec2key(), nss, typeConverter);
    }

    /**
     * Parses a given JavaBlock using cd as context to determine the right
     * references.
     * @param block a String describing a java block
     * @param cd ClassDeclaration representing the context in which the
     * block has to be interpreted.
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlock(String block, ClassDeclaration cd,
            NamespaceSet nss){
        return createRecoder2KeY(nss).readBlock(block, new Context
            (sc, (recoder.java.declaration.ClassDeclaration)
	     rec2key().toRecoder(cd)));
    }


    /**
     * Parses a given JavaBlock using an empty context.
     * @param block a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readJavaBlock(String block, NamespaceSet nss) {
        return createRecoder2KeY(nss).readBlockWithEmptyContext(block);
    }


    public ImmutableList<KeYJavaType> findImplementations
	(Type ct, String name, ImmutableList<KeYJavaType> signature) {

        // set up recoder inputs
        recoder.abstraction.ClassType rct =
         (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        // transform the signature up to recoder conventions
        ArrayList<recoder.abstraction.Type> rsignature =
            new ArrayList<recoder.abstraction.Type>(signature.size());
        Iterator<KeYJavaType> i = signature.iterator();
        int j = 0;
        while (i.hasNext()) {
            rsignature.add(j, (recoder.abstraction.Type)
            rec2key().toRecoder(i.next()));
            j++;
        }

        // If ct is an interface, but does not declare the method, we
	// need to start the search "upstairs"

        while(rct.isInterface() && !isDeclaringInterface(rct, name, rsignature)) {
	     rct = rct.getAllSupertypes().get(1);
	}


        ImmutableList<KeYJavaType> classList = ImmutableSLList.<KeYJavaType>nil();
	classList = recFindImplementations(rct, name, rsignature, classList);


        if ( !declaresApplicableMethods(rct, name, rsignature)) {
            // ct has no implementation, go up
            List<recoder.abstraction.ClassType> superTypes = rct.getAllSupertypes();
            int k=0;
            while (k<superTypes.size() &&
		   !declaresApplicableMethods(superTypes.get(k),
                                              name, rsignature)) k++;
	    if (k<superTypes.size()) {
		rct = superTypes.get(k);
		KeYJavaType r = (KeYJavaType)mapping.toKeY(rct);
		if (r==null) {
		    System.out.println("Type "+rct.getName());
		} else {
		    classList = classList.append(r);
		}
	    } // no implementation is needed if classes above are abstract
        }

        return classList;
    }


    private ImmutableList<KeYJavaType> recFindImplementations(
                                        recoder.abstraction.ClassType ct,
                                        String name,
                                        List<recoder.abstraction.Type> signature,
					ImmutableList<KeYJavaType> result) {
        recoder.service.CrossReferenceSourceInfo si
	    = getServConf().getCrossReferenceSourceInfo();

        if (declaresApplicableMethods(ct, name, signature)) {
	    KeYJavaType r = (KeYJavaType)mapping.toKeY(ct);
	    if (r==null) {
		System.out.println("Type "+ct.getFullName()+":"+name+" not found");
	    } else if (!result.contains(r)){
		result = result.prepend(r);
	    }
        }

        List<recoder.abstraction.ClassType> classes = si.getSubtypes(ct);

        //alpha sorting to make order deterministic
        recoder.abstraction.ClassType[] classesArray =
                classes.toArray(new recoder.abstraction.ClassType[classes.size()]);
        java.util.Arrays.sort(classesArray, new java.util.Comparator<recoder.abstraction.ClassType>() {
            public int compare(recoder.abstraction.ClassType o1, recoder.abstraction.ClassType o2) {
                return o2.getFullName().compareTo(o1.getFullName());
            }
        });

        for (recoder.abstraction.ClassType c : classesArray) {
            result = recFindImplementations(c, name, signature, result);
        }
        return result;
    }


    private boolean declaresApplicableMethods(recoder.abstraction.ClassType ct,
					      String name,
					      List<recoder.abstraction.Type> signature) {
        recoder.service.CrossReferenceSourceInfo si
	    = getServConf().getCrossReferenceSourceInfo();

	List<recoder.abstraction.Method> list = si.getMethods(ct);
	int s = list.size();
	int i = 0;
	while (i < s) {
	    recoder.abstraction.Method m = list.get(i);
	    if (name.equals(m.getName())
		&& si.isCompatibleSignature(signature, m.getSignature())
		&& si.isVisibleFor(m, ct)
		&& !m.isAbstract()) return true;
	    else i++;
	}
	return false;
    }

    private boolean isDeclaringInterface(recoder.abstraction.ClassType ct,
					 String name,
					 List<recoder.abstraction.Type> signature) {
        recoder.service.CrossReferenceSourceInfo si
	    = getServConf().getCrossReferenceSourceInfo();

	Debug.assertTrue(ct.isInterface());

	List<recoder.abstraction.Method> list = si.getMethods(ct);
	int s = list.size();
	int i = 0;
	while (i < s) {
	    recoder.abstraction.Method m = list.get(i);
	    if (name.equals(m.getName())
		&& si.isCompatibleSignature(signature, m.getSignature())
		&& si.isVisibleFor(m, ct)) return true;
	    else i++;
	}
	return false;
    }

    public void putImplicitMethod(IProgramMethod m, KeYJavaType t) {
	HashMap<String, IProgramMethod> map = implicits.get(t);
	if (map==null) {
	    map = new LinkedHashMap<String, IProgramMethod>();
	    implicits.put(t, map);
	}
	map.put(m.name().toString(), m);
    }


    public KeYProgModelInfo copy() {
 	return new KeYProgModelInfo(services, getServConf(), rec2key().copy(),
 				    typeConverter);
    }
}
