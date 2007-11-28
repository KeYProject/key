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
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.SLListOfProgramMethod;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYExceptionHandler;

public class KeYProgModelInfo{


    private KeYCrossReferenceServiceConfiguration sc = null;
    private KeYRecoderMapping mapping;
    private TypeConverter typeConverter;
    private HashMap implicits = new HashMap();
    private KeYExceptionHandler exceptionHandler = null;
    
    public KeYProgModelInfo(TypeConverter typeConverter, 
            KeYExceptionHandler keh){
 	this(new KeYCrossReferenceServiceConfiguration(keh), 
	     new KeYRecoderMapping(), typeConverter);
	exceptionHandler = keh;
    }

    KeYProgModelInfo(KeYCrossReferenceServiceConfiguration crsc,
		     KeYRecoderMapping krm, TypeConverter typeConverter) {
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

    public Set allElements(){
        return rec2key().elemsKeY();
    }
    
    
    /**
     * Returns all ObjectSorts mapped to java.Types in KeY.
     * @return a Collection containing the ObjectSorts.
     */
    public Collection allObjectSorts(){
	Set result=new HashSet();
	Iterator it=allElements().iterator();
	while (it.hasNext()) {
	    Object o=it.next();
	    if (o instanceof KeYJavaType &&
		(((KeYJavaType)o).getSort() instanceof ObjectSort)) {
	        result.add(((KeYJavaType)o).getSort());
            }
	}
        return result;
    }


    private recoder.list.MethodList getAllRecoderMethods(KeYJavaType kjt){
	if (kjt.getJavaType() instanceof TypeDeclaration) {
	    Object o = rec2key().toRecoder(kjt);
	    if (o instanceof recoder.abstraction.ClassType) {
		recoder.abstraction.ClassType rtd
		    = (recoder.abstraction.ClassType) o;
		return rtd.getAllMethods();
	    }
	}
	return new recoder.list.MethodArrayList();
	
    }


    /**Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     * @return the list of visible methods of this type and its supertypes.
     */

    public ListOfMethod getAllMethods(KeYJavaType kjt) {
        recoder.list.MethodList rmethods=getAllRecoderMethods(kjt);
        ListOfMethod result = SLListOfMethod.EMPTY_LIST;
        for (int i=rmethods.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rmethods.getMethod(i);
            Method m= 
		((ProgramMethod)rec2key().toKeY(rm)).getMethodDeclaration();
            result=result.prepend(m);
        }
        return result;
    }


    /**Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     * @return the list of visible methods of this type and its supertypes.
     */

    public ListOfProgramMethod getAllProgramMethods(KeYJavaType kjt) {
        recoder.list.MethodList rmethods=getAllRecoderMethods(kjt);
        ListOfProgramMethod result = SLListOfProgramMethod.EMPTY_LIST;
        for (int i=rmethods.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rmethods.getMethod(i);
            ProgramMethod m=(ProgramMethod)rec2key().toKeY(rm);
	    if (m!=null) {
		result=result.prepend(m);
	    } 
        }
        return result;
    }



    private recoder.list.TypeList getRecoderTypes(ListOfType types) {
        if (types==null) {
            return null;
        }
        IteratorOfType it=types.iterator();
        recoder.list.TypeArrayList tl
            = new recoder.list.TypeArrayList(types.size());
        while (it.hasNext()) {
	    Type n = it.next();
            tl.add( (recoder.abstraction.Type) rec2key().toRecoder(n));
        }
        return tl;
    }

    private recoder.list.TypeList getRecoderTypes(ListOfKeYJavaType types) {
        if (types==null) {
            return null;
        }
        IteratorOfKeYJavaType it=types.iterator();
        recoder.list.TypeArrayList tl
            = new recoder.list.TypeArrayList(types.size());
        while (it.hasNext()) {
            final KeYJavaType kjt = it.next();  
            tl.add( (recoder.abstraction.Type) rec2key().toRecoder(kjt));
        }
        return tl;
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
     * checls wheter subType is assignment compatible to type according 
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

    private recoder.list.MethodList getRecoderMethods(KeYJavaType ct){
        recoder.abstraction.ClassType rct
            = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        return rct.getProgramModelInfo().getMethods(rct);
    }
    
    private recoder.list.ConstructorList getRecoderConstructors(KeYJavaType ct){
        recoder.abstraction.ClassType rct
            = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        return rct.getProgramModelInfo().getConstructors(rct);
    }    

    private recoder.list.MethodList getRecoderMethods
	(KeYJavaType ct, String m, ListOfType signature, KeYJavaType context){
        recoder.abstraction.ClassType rct
            = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        recoder.abstraction.ClassType rcontext
            = (recoder.abstraction.ClassType) rec2key().toRecoder(context);
        return rct.getProgramModelInfo().getMethods(rct, m,
						    getRecoderTypes(signature),
						    rcontext);
    }


    private recoder.list.MethodList getRecoderMethods
	(KeYJavaType ct, String m, ListOfKeYJavaType signature, 
	 KeYJavaType context){
        final recoder.abstraction.ClassType rct
            = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        final recoder.abstraction.ClassType rcontext
            = (recoder.abstraction.ClassType) rec2key().toRecoder(context); 
        return rct.getProgramModelInfo().getMethods(rct, m,
						    getRecoderTypes(signature),
						    rcontext);
    }

    private recoder.list.ConstructorList getRecoderConstructors
	(KeYJavaType ct, ListOfKeYJavaType signature){
        recoder.abstraction.ClassType rct
            = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
	recoder.list.ConstructorList res = rct.getProgramModelInfo().getConstructors
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

    public ListOfMethod getMethods(KeYJavaType ct, String m,
				   ListOfType signature, KeYJavaType context){
        recoder.list.MethodList rml = 
	    getRecoderMethods(ct, m, signature, context);
        ListOfMethod result = SLListOfMethod.EMPTY_LIST;
        for (int i=rml.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rml.getMethod(i);
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

    public ListOfMethod getMethods(KeYJavaType ct){
        recoder.list.MethodList rml = getRecoderMethods(ct);
        ListOfMethod result = SLListOfMethod.EMPTY_LIST;
        for (int i=rml.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rml.getMethod(i);
	    if(!(rm instanceof recoder.bytecode.MethodInfo)){
		Method m = ((ProgramMethod) rec2key().toKeY(rm)).
		    getMethodDeclaration();
		result=result.prepend(m);
	    }
        }
        return result;
    }

	/**
	 * Returns the ProgramMethods locally defined within the given
	 * class type. If the type is represented in source code,
	 * the returned list matches the syntactic order.
	 * @param ct a class type.
	 */
    public ListOfProgramMethod getAllProgramMethodsLocallyDeclared(KeYJavaType ct){
        recoder.list.MethodList rml = getRecoderMethods(ct);
        ListOfProgramMethod result = SLListOfProgramMethod.EMPTY_LIST;
        for (int i=rml.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rml.getMethod(i);
	    if(!(rm instanceof recoder.bytecode.MethodInfo)){
		result = result.prepend((ProgramMethod) rec2key().toKeY(rm));
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

    public ListOfProgramMethod getConstructors(KeYJavaType ct){
        recoder.list.ConstructorList rcl = getRecoderConstructors(ct);
        ListOfProgramMethod result = SLListOfProgramMethod.EMPTY_LIST;
        for (int i=rcl.size()-1; i>=0; i--) {
            recoder.abstraction.Method rm=rcl.getConstructor(i);
	    ProgramMethod m=(ProgramMethod) rec2key().toKeY(rm);
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
     * @param signature ListOfKeYJavaType representing the signature of the constructor
     * @return the most specific constructor declared in the given type 
     */
    public Constructor getConstructor(KeYJavaType ct, 
				      ListOfKeYJavaType signature) {
        recoder.list.ConstructorList constructors =
            getRecoderConstructors(ct, signature);
        if (constructors.size()==1) {
	    Object o = rec2key().toKeY(constructors.getConstructor(0));
	    if(o instanceof Constructor){
		return (Constructor) o;
	    }
	    if(o instanceof ProgramMethod){
		return (Constructor) ((ProgramMethod) o).getMethodDeclaration();
	    }
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
    private ProgramMethod getImplicitMethod(KeYJavaType ct, String name) {
	HashMap m=(HashMap)implicits.get(ct);
	if (m!=null) {
	    ProgramMethod pm = (ProgramMethod)m.get(name);
	    if (pm!=null) {
		return pm;
	    }
	}       	
 	TypeDeclaration cd = (TypeDeclaration)ct.getJavaType();
 	ArrayOfMemberDeclaration members = cd.getMembers();
 	for (int i = 0; i<members.size(); i++) {
 	    MemberDeclaration member = members.getMemberDeclaration(i);
 	    if (member instanceof ProgramMethod &&
 		((ProgramMethod)member).getMethodDeclaration().getName().equals(name)) {
 		return (ProgramMethod)member;
 	    }
 	}
 	Debug.out("keyprogmodelinfo: implicit method %1 not found in %2 (%1, %2) ", 
 		  name, ct);
 	return null;
    }

    /**
     * Returns the programmethods with the given name that is defined
     * in the given type or in a supertype where it is visible for the
     * given type, and has a signature that is compatible to the given one.
     * In the case that no method has been found or that the method could not
     * be resolved uniquely <code>null</code> is returned. 
     * @param ct the class type to get methods from.
     * @param m the name of the methods in question.
     * @param signature the statical type signature of a callee.
     * @return the programmethod, if one is found,
     * null if none or more than one programmethod is found (in this case
     * a debug output is written to console).
     */
    public ProgramMethod getProgramMethod(KeYJavaType ct, String m,
					  ListOfType signature, 
					  KeYJavaType context) {
	if (ct.getJavaType() instanceof ArrayType ||
	    context.getJavaType() instanceof ArrayType) {
	    return getImplicitMethod(ct, m);
	}
        
        recoder.list.MethodList methodlist =
            getRecoderMethods(ct, m, signature, context);		
        if (methodlist.size()==1) {
            return (ProgramMethod) rec2key().toKeY(methodlist.getMethod(0));
        } 
        
        Debug.out("Program Method not found: ", m);
        return null;
    }


    /**
     * Returns the programmethods with the given name that is defined
     * in the given type or in a supertype where it is visible for the
     * given type, and has a signature that is compatible to the given one.
     * @param ct the class type to get methods from.
     * @param m the name of the methods in question.
     * @param signature the statical type signature of a callee.
     * @return the programmethod, if one is found,
     * null if none or more than one programmethod is found (in this case
     * a debug output is written to console).
     */
    public ProgramMethod getProgramMethod(KeYJavaType ct, String m,
					  ListOfKeYJavaType signature,
					  KeYJavaType context) {
	if (ct.getJavaType() instanceof ArrayType || 
	    context.getJavaType() instanceof ArrayType) {
            return getImplicitMethod(ct, m);
	}
     
	recoder.list.MethodList methodlist = 
            getRecoderMethods(ct, m, signature, context);		

        if (methodlist.size()==1) {
            return (ProgramMethod) rec2key().toKeY(methodlist.getMethod(0));
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
     * @param rfl the ListOfField to be looked up
     * @return list with the corresponding fields as KeY datastructures
     */
    private ListOfField asKeYFields(recoder.list.FieldList rfl) {
        ListOfField result = SLListOfField.EMPTY_LIST;
        if(rfl == null){
            // this occurs for the artificial Null object at the moment
            // should it have implicit fields?
            return result;
        }
        for (int i=rfl.size()-1; i>=0; i--) {
            recoder.abstraction.Field rf = rfl.getField(i);
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
    public ListOfField getAllFieldsLocallyDeclaredIn(KeYJavaType ct){
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
    public ListOfField getAllVisibleFields(KeYJavaType ct){
        if (ct.getJavaType() instanceof ArrayDeclaration) {
            return getVisibleArrayFields(ct);
        }
        
        recoder.abstraction.ClassType rct
        = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        recoder.list.FieldList rfl =
            rct.getProgramModelInfo().getAllFields(rct);        
        return asKeYFields(rfl);
    }

    /**
     * returns all fields of and visible in an array field 
     * @param arrayType the KeYJavaType of the array
     * @return the list of visible fields
     */
    private ListOfField getVisibleArrayFields(KeYJavaType arrayType) {
        ListOfField result = SLListOfField.EMPTY_LIST;
        
        final ArrayOfMemberDeclaration members = 
            ((ArrayDeclaration)arrayType.getJavaType()).getMembers();
        
        for (int i = members.size()-1; i>=0; i--){
            final MemberDeclaration member = members.getMemberDeclaration(i); 
            if (member instanceof FieldDeclaration) {
                final ArrayOfFieldSpecification specs = 
                    ((FieldDeclaration)member).getFieldSpecifications();                
                for (int j = specs.size() - 1; j>=0; j--) {
                    result = result.prepend(specs.getFieldSpecification(j));
                }
            }
        }
                        
        //      fields of java.lang.Object visible in an array
        final ListOfField javaLangObjectField = 
            getAllVisibleFields((KeYJavaType)rec2key().
                                toKeY(sc.getNameInfo().getJavaLangObject()));
                
        final IteratorOfField it = javaLangObjectField.iterator();
        while (it.hasNext()) {
           final Field f = it.next();
           
           if (!((recoder.abstraction.Field)
                   rec2key().toRecoder(f)).isPrivate()){
               result = result.append(f);
           }
        }                          
        return result;
    }

    /**
     * returns all proper subtypes of class <code>ct</code> (i.e. without <code>ct</code> itself)      
     */
    private recoder.list.ClassTypeList getAllRecoderSubtypes(KeYJavaType ct){
        return sc.getCrossReferenceSourceInfo().
            getAllSubtypes((recoder.abstraction.ClassType)rec2key().toRecoder(ct));
    }
    
    /**
     * returns all supertypes of the given class type with the type itself as
     * first element    
     */
    private recoder.list.ClassTypeList getAllRecoderSupertypes(KeYJavaType ct){
        return sc.getCrossReferenceSourceInfo().
           getAllSupertypes((recoder.abstraction.ClassType)rec2key().toRecoder(ct));
    }
    

    /**
     * returns a list of KeYJavaTypes representing the given recoder types in
     * the same order
     * @param rctl the ClassTypeList to be converted
     * @return list of KeYJavaTypes representing the given recoder types in
     * the same order
     */
    private ListOfKeYJavaType asKeYJavaTypes(final recoder.list.ClassTypeList rctl) {
        ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST;
        for (int i=rctl.size()-1; i>=0 ; i--){
            final recoder.abstraction.ClassType rct = rctl.getClassType(i);
            final KeYJavaType kct = (KeYJavaType)rec2key().toKeY(rct);
            result = result.prepend(kct);
        }
        return result;
    }

    /**
     * Returns all known subtypes of the given class type.
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ListOfKeYJavaType getAllSupertypes(KeYJavaType ct){
        return asKeYJavaTypes(getAllRecoderSupertypes(ct));        
    }

    /**
     * Returns all proper subtypes of the given class type
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ListOfKeYJavaType getAllSubtypes(KeYJavaType ct){        
        return asKeYJavaTypes(getAllRecoderSubtypes(ct));                
    }
    
    private Recoder2KeY createRecoder2KeY(NamespaceSet nss) {
	return new Recoder2KeY(sc, rec2key(), nss, typeConverter);
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
    
   
    public ListOfKeYJavaType findImplementations
	(Type ct, String name, ListOfKeYJavaType signature) {

        // set up recoder inputs
        recoder.abstraction.ClassType rct =
         (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        // transform the signature up to recoder conventions
        recoder.list.TypeArrayList rsignature = 
            new recoder.list.TypeArrayList(signature.size());
        IteratorOfKeYJavaType i = signature.iterator();
        int j = 0;
        while (i.hasNext()) {
            rsignature.insert(j, (recoder.abstraction.Type)
            rec2key().toRecoder(i.next()));
            j++;
        }

        // If ct is an interface, but does not declare the method, we
	// need to start the search "upstairs"

        while(rct.isInterface() && !isDeclaringInterface(rct, name, rsignature)) {
	     rct = rct.getAllSupertypes().getClassType(1);
	}


        ListOfKeYJavaType classList = SLListOfKeYJavaType.EMPTY_LIST;
	classList = recFindImplementations(rct, name, rsignature, classList);


        if ( !declaresApplicableMethods(rct, name, rsignature)) {
            // ct has no implementation, go up
            recoder.list.ClassTypeList superTypes = rct.getAllSupertypes();
            int k=0;
            while (k<superTypes.size() &&
		   !declaresApplicableMethods(superTypes.getClassType(k),
                                              name, rsignature)) k++;
	    if (k<superTypes.size()) {
		rct = superTypes.getClassType(k);
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


    private ListOfKeYJavaType recFindImplementations(
                                        recoder.abstraction.ClassType ct,
                                        String name,
                                        recoder.list.TypeList signature,
					ListOfKeYJavaType result) {
        recoder.service.CrossReferenceSourceInfo si 
	    = getServConf().getCrossReferenceSourceInfo();

        if (declaresApplicableMethods(ct, name, signature)) {
	    KeYJavaType r = (KeYJavaType)mapping.toKeY(ct);
	    if (r==null) {
		System.out.println("Type "+ct.getFullName()+":"+name+" not found");
	    } else {
		result = result.prepend(r);
	    }
        }

        recoder.list.ClassTypeList classes = si.getSubtypes(ct);


        //alpha sorting to make order deterministic
        recoder.abstraction.ClassType[] classesArray = 
            classes.toClassTypeArray();
        java.util.Arrays.sort(classesArray, new java.util.Comparator() {
            public int compare(Object o1, Object o2) {
                recoder.abstraction.ClassType c1 = 
                    (recoder.abstraction.ClassType) o1;
                recoder.abstraction.ClassType c2 = 
                    (recoder.abstraction.ClassType) o2;
                return -c1.getFullName().compareTo(c2.getFullName());
            }
        });

        for (int i = 0; i <classesArray.length; i++) {
            recoder.abstraction.ClassType c = classesArray[i];
            result = recFindImplementations(c, name, signature, result);
        }
        return result;
    }


    private boolean declaresApplicableMethods(recoder.abstraction.ClassType ct,
					      String name,
					      recoder.list.TypeList signature) {
        recoder.service.CrossReferenceSourceInfo si 
	    = getServConf().getCrossReferenceSourceInfo();
	
	recoder.list.MethodList list = si.getMethods(ct);
	int s = list.size();
	int i = 0;
	while (i < s) {
	    recoder.abstraction.Method m = list.getMethod(i);
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
					 recoder.list.TypeList signature) {
        recoder.service.CrossReferenceSourceInfo si 
	    = getServConf().getCrossReferenceSourceInfo();
	
	Debug.assertTrue(ct.isInterface());
	
	recoder.list.MethodList list = si.getMethods(ct);
	int s = list.size();
	int i = 0;
	while (i < s) {
	    recoder.abstraction.Method m = list.getMethod(i);
	    if (name.equals(m.getName())
		&& si.isCompatibleSignature(signature, m.getSignature())
		&& si.isVisibleFor(m, ct)) return true;
	    else i++;
	}
	return false;
    }

    public void putImplicitMethod(ProgramMethod m, KeYJavaType t) {
	HashMap map = (HashMap)implicits.get(t);
	if (map==null) {
	    map = new HashMap();
	    implicits.put(t, map);
	}
	map.put(m.name().toString(), m);
    }
    

    public KeYProgModelInfo copy() {
 	return new KeYProgModelInfo(getServConf(), rec2key().copy(), 
 				    typeConverter);
    }
    

}




