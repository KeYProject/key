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


package de.uka.ilkd.key.java.recoderext;

import java.util.ArrayList;
import java.util.List;

import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.abstraction.TypeParameter;
import recoder.bytecode.*;
import recoder.io.DataLocation;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.PackageSpecification;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Private;
import recoder.java.reference.EnumConstructorReference;
import recoder.java.reference.PackageReference;
import recoder.java.reference.TypeReference;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.util.Debug;

/**
 * Make a ClassDeclaration out of a class file.
 * 
 * Given a ClassFile read in via recoder create a corresponding ClassDeclaration
 * to be registered in the system instead. This allows to rely on one
 * mechanism of Recoder-KeY correspondance.
 * 
 * The information from the classfile are not retrieved via the various services
 * but via direct queries. This makes sure that the classfile is not known to 
 * a classfile repository and saves space.
 * 
 * Method bodies cannot be retrieved so that all methods/constructors have got a
 * "null-body", the resulting declaration is a stub.
 * 
 * The information is stored into a compilation unit within the appropriate package.
 * 
 * TODO Recoder does not allow to detect if an inner class is static or not because 
 * it discards the information about inner classes all to early. That is why all inner
 * classes are non-static. Does this matter?  Patch is on the way
 * 
 * TODO inner classes are not detected to be "private". A combination of private and 
 * static seems impossible with recoder
 * 
 * TODO Possible improvement: Remove "synthetic" members (JVM spec chapter 4)
 * 
 * @see ClassFileDeclarationManager
 * @author MU
 */

public class ClassFileDeclarationBuilder implements Comparable<ClassFileDeclarationBuilder> {

    // used to create elements
    private ProgramFactory factory;

    // unit under investigation
    private ClassFile classFile;
    
    // the physical name stored in the class file
    private String physicalName;
    
    // the result
    private CompilationUnit compilationUnit;

    // the class or interface declaration
    private TypeDeclaration typeDecl;

    // this is the location for error messages etc.
    private DataLocation dataLocation;

    // the member to the declaration are collected here
    private ASTList<MemberDeclaration> memberDecls;

    // the manager to which this builder belongs
    private ClassFileDeclarationManager manager;
    
    // store all type parameters of this class and potentially 
    // all enclosing classes
    private List<TypeParameterInfo> typeParameters;

    /**
     * create a new ClassDeclaration builder. The builder can be used to create a
     * ClassDeclaration for a single class file.
     * 
     * @param classFile class file to be investigated
     * @param manager the manager to which this builder belongs 
     */
    public ClassFileDeclarationBuilder(ClassFileDeclarationManager manager, ClassFile classFile) {
        this.factory = manager.getProgramFactory();
        this.manager = manager;
        this.classFile = classFile;
        this.physicalName = classFile.getPhysicalName();
    }

    
    /**
     * get the class name stored in the class file. May contain '$' for inner or
     * anonymous classes
     * 
     * @return the physical name of the class in the class file
     */
    public String getFullClassname() {
        return physicalName;
    }
    
    
    /**
     * get the class name of this class. If it is an inner class, it is only the
     * part after $, or the complete short name otherwise. Anonymous classes are
     * therefore referenced by "EnclosingClass$11" for instance.
     * 
     * @return the name of the class
     */
    public String getClassName() {
        if (isInnerClass())
            return physicalName.substring(physicalName.lastIndexOf('$') + 1);
        else
            return physicalName.substring(physicalName.lastIndexOf('.') + 1);
    }
    
    /**
     * retrieve the compilation unit for the class file under consideration.
     * 
     * The second and following calls will return the cached value of the initial
     * calculation.
     * 
     * This method calls {@link #makeTypeDeclaration()} and embeds this type
     * into a compilation unit.
     * 
     * @return a compilation unit corresponding to the class file.
     */
    public CompilationUnit makeCompilationUnit() {
        if (compilationUnit == null) {
            compilationUnit = new CompilationUnit();
            setPackage();
            makeTypeDeclaration();
            addTypeDeclarationToCompUnit();
            compilationUnit.makeAllParentRolesValid();
            compilationUnit.setDataLocation(dataLocation);
        }
        return compilationUnit;
    }

    /**
     * retrieve a TypeDeclaration for the class file under consideration
     * 
     * The second and following calls will return the cached value of the
     * initial calculation.
     * 
     * @return a TypeDeclaration corresponding to the class file
     */
    public TypeDeclaration makeTypeDeclaration() {
        
        if(typeDecl == null) {
            createTypeDeclaration();
            setNameAndMods();
            setInheritance();
            memberDecls = new ASTArrayList<MemberDeclaration>();
            if (typeDecl instanceof EnumDeclaration) {
                for (FieldInfo field : classFile.getFieldInfos()) {
                    if(isEnumConstant(field))
                        addEnumConstant(field);
                }
                // create a default constructor for the enum constants
                addDefaultConstructor();
            }
            for (ConstructorInfo constr : classFile.getConstructorInfos()) {
                addConstructor(constr);
            }
            for (FieldInfo field : classFile.getFieldInfos()) {
                if(!isEnumConstant(field))
                    addField(field);        
            }
            for (MethodInfo method : classFile.getMethodInfos()) {
                addMethod(method);
            }
            typeDecl.setMembers(memberDecls);
            typeDecl.makeAllParentRolesValid();
        }
        return typeDecl;
    }
    
    /**
     * set the location to be stored in the compilation unit, mainly for
     * error reporting.
     * 
     * @param dataLocation the DataLocation to be set or null 
     */
    public void setDataLocation(DataLocation dataLocation) {
        this.dataLocation = dataLocation;
    }
    
    /**
     * is the considered ClassFile the byte code of an inner class?
     * 
     * This is done checking the fully qualified class name. Does it contain a
     * "$" and is this character not followed by a number
     * 
     * @return true iff the classFile under inspection is an inner class
     */
    public boolean isInnerClass() {
        if(physicalName.contains("$")) {
            String trailing = physicalName.substring(physicalName.lastIndexOf('$') + 1);
            return !startsWithADigit(trailing);
        }
        return false;
    }
    
    /**
     * is the considered ClassFile the representation of an anymous class or a class
     * declared within a program?
     * 
     * This is the case if the last $ is followed by a digit.
     * 
     * @return true iff the classFile under inspection is an anon. or in-code-class
     */
    public boolean isAnonymousClass() {
        if(physicalName.contains("$")) {
            String trailing = physicalName.substring(physicalName.lastIndexOf('$') + 1);
            return startsWithADigit(trailing);
        }
        return false;
    }
    
    /**
     * If this is a builder for an inner class, the declaration has to be
     * attached to the enclosing class. This method adds the resulting
     * declaration to an existing type declaration. A reference to the
     * enclosing builder is stored to retrieve the type parameter
     * information, e.g.
     * 
     */
    public void attachToEnclosingDeclaration() {
        if(!isInnerClass())
            throw new IllegalStateException("only inner classes can be attached to enclosing classes");

        // this builder must not yet have built:
        assert typeDecl == null;

        ClassFileDeclarationBuilder enclBuilder = manager.getBuilder(getEnclosingName());
        TypeDeclaration enclTD = enclBuilder.makeTypeDeclaration();
        ASTList<MemberDeclaration> members = enclTD.getMembers();
        assert members != null : "ClassDeclaration with null members!";
        TypeDeclaration childtd = makeTypeDeclaration();
        members.add(childtd);
        enclTD.makeParentRoleValid();
    }
    
    /**
     * get the fully qualified name of the enclosing class of an inner class
     * @return class name, not null
     */
    public String getEnclosingName() {
        if(!isInnerClass() && !isAnonymousClass())
            throw new IllegalStateException("only inner classes have an enclosing class");
        return physicalName.substring(0, physicalName.lastIndexOf('$'));
    }

    /**
     * make a stub class declaration for a fully qualified type reference.
     * 
     * If the type reference stands for an array, the trailing [] are
     * discarded first.
     * 
     * 
     * @param programFactory
     *                factory to use as parser
     * @param fullClassName
     *                the fully qualified type name
     * @return a compilation unit that has not been added to a source repository
     *         yet
     * @throws ParserException
     *                 thrown by the parser
     */
    public static CompilationUnit makeEmptyClassDeclaration(
            ProgramFactory programFactory, 
            String fullClassName) 
                      throws ParserException {
        
        while(fullClassName.endsWith("[]"))
            fullClassName = fullClassName.substring(0, fullClassName.length()-2);
        
        String cuString = "";
        int lastdot = fullClassName.lastIndexOf('.');
        if(lastdot != -1) {
            // there is a package
            cuString = "package " + fullClassName.substring(0, lastdot) + "; ";
        }
        
        cuString += "public class " + fullClassName.substring(lastdot+1) + " { }";

        Debug.out("Parsing: " + cuString);
        
        return programFactory.parseCompilationUnit(cuString);
    }
    
    

    
    // --------------------------------------- private stuff below this line (and main)

      
    /*
     * create the target declaration and register it in the comp. unit
     */
    private void createTypeDeclaration() {
        
        if (classFile.isInterface()) {
            typeDecl = factory.createInterfaceDeclaration();
        } else if (classFile.isOrdinaryClass()) {
            typeDecl = factory.createClassDeclaration();
        } else if (classFile.isEnumType()){
            // there is no factory.createEnumDeclaration()
            typeDecl = new EnumDeclaration(); 
        } else {
            throw new ConvertException("Only Interfaces, enums and classes are allowed as byte code files");
        }
    }
    
    /*
     * add the type declaration to the compilation unit
     */
    
    private void addTypeDeclarationToCompUnit() {
        ASTArrayList<TypeDeclaration> dl = new ASTArrayList<TypeDeclaration>(1);
        dl.add(typeDecl);
        compilationUnit.setDeclarations(dl);
    }

    /*
     * set the name and modifiers of the class/intf declaration
     */
    private void setNameAndMods() {
        typeDecl.setIdentifier(factory.createIdentifier(getClassName()));

        ASTArrayList<DeclarationSpecifier> specs = new ASTArrayList<DeclarationSpecifier>();

        if (classFile.isAbstract())
            specs.add(factory.createAbstract());
        if (classFile.isPublic())
            specs.add(factory.createPublic());
        if (classFile.isFinal())
            specs.add(factory.createFinal());
        if (classFile.isStrictFp())
            specs.add(factory.createStrictFp());
        if (classFile.isStatic())
            specs.add(factory.createStatic());

        typeDecl.setDeclarationSpecifiers(specs);
    }

    /*
     * set super types, and implemented (or extended) interfaces
     */    
    private void setInheritance() {
        
        // do not inherit Object from itself!
        if("java.lang.Object".equals(physicalName))
            return;
        
        String superClassName = classFile.getSuperClassName();
        String[] interfaceNames = classFile.getInterfaceNames();
        
        if (typeDecl instanceof ClassDeclaration) {
            ClassDeclaration classDecl = (ClassDeclaration) typeDecl;
            TypeReference tyRef = createTypeReference(superClassName);
            Extends ext = factory.createExtends(tyRef);
            classDecl.setExtendedTypes(ext);
            
            ASTList<TypeReference> implList = new ASTArrayList<TypeReference>();
            for (String intf : interfaceNames) {
                implList.add(createTypeReference(intf));
            }
            if(implList.size() > 0)
                classDecl.setImplementedTypes(factory.createImplements(implList));
        } else if(typeDecl instanceof EnumDeclaration) { 
            EnumDeclaration enDecl = (EnumDeclaration) typeDecl;
            ASTList<TypeReference> implList = new ASTArrayList<TypeReference>();
            for (String intf : interfaceNames) {
                implList.add(createTypeReference(intf));
            }
            if(implList.size() > 0)
                enDecl.setImplementedTypes(factory.createImplements(implList));
        } else if(typeDecl instanceof InterfaceDeclaration){
            InterfaceDeclaration intfDecl = (InterfaceDeclaration) typeDecl;
            ASTList<TypeReference> implList = new ASTArrayList<TypeReference>();
            for (String intf : interfaceNames) {
                implList.add(createTypeReference(intf));
            }
            if(implList.size() > 0)
                intfDecl.setExtendedTypes(factory.createExtends(implList));
        } else
           throw new Error("unknown declaration type: " + typeDecl.getClass().getName());
        
    }

    /*
     * add a package specification if not in the default package.
     */
    private void setPackage() {
        int packIndex = physicalName.lastIndexOf('.');
        // default package: job done
        if (packIndex < 0)
            return;
        String packName = physicalName.substring(0, packIndex);
        PackageReference ref = makePackageReference(packName);
        PackageSpecification p = factory.createPackageSpecification(ref);
        compilationUnit.setPackageSpecification(p);
    }



    /*
     * create the modifier list for a field declaration
     * TODO are these all the possible modifiers?
     */
    private ASTList<DeclarationSpecifier> makeFieldSpecifiers(FieldInfo decl) {
        ASTList<DeclarationSpecifier> specs = new ASTArrayList<DeclarationSpecifier>();
        if (decl.isPrivate())
            specs.add(factory.createPrivate());
        if (decl.isProtected())
            specs.add(factory.createProtected());
        if (decl.isPublic())
            specs.add(factory.createPublic());
        if (decl.isStatic())
            specs.add(factory.createStatic());
        if (decl.isFinal())
            specs.add(factory.createFinal());
        return specs;
    }

    /*
     * This uses an undocumented(!) feature which is provided by the java
     * compiler: Enum constants have set the bit 0x4000 in their access flags.
     * TODO find a documented and transferable mean to express this 
     */
    private boolean isEnumConstant(FieldInfo field) {
        return ((field.getAccessFlags() & 0x4000) == 0x4000);
    }

    /*
     * Add a field to the member list
     * TODO compile time constants.
     */
    private void addField(FieldInfo field) {
        
        // ignore internal fields.
        String name = field.getName();
        if(isInternal(name))
            return;
        
        String typename = field.getTypeName();
        typename = resolveTypeVariable(typename, null);
        TypeReference type = createTypeReference(typename);
        Identifier id = factory.createIdentifier(name);
        FieldDeclaration decl = factory.createFieldDeclaration(type, id);

        decl.setDeclarationSpecifiers(makeFieldSpecifiers(field));
        
        memberDecls.add(decl);
    }

    /*
     * Add an enum constant to the member list.
     * There is no factory.createEnum... () method
     * 
     * TODO This maps all constants w/o arguments, i.e. 
     * such a constructor must be present. :( 
     */
    private void addEnumConstant(FieldInfo field) {
        Identifier id = factory.createIdentifier(field.getName());
        EnumConstructorReference ecr = new EnumConstructorReference();
        EnumConstantSpecification ecs = new EnumConstantSpecification(id, ecr);
        EnumConstantDeclaration ecd = new EnumConstantDeclaration(ecs, new ASTArrayList<DeclarationSpecifier>());
        memberDecls.add(ecd);
    }
  
    /*
     * create the modifier list for a method declaration
     * TODO are these all the possiblie mods?
     */
    private ASTList<DeclarationSpecifier> makeMethodSpecifiers(MethodInfo decl) {
        ASTList<DeclarationSpecifier> specs = new ASTArrayList<DeclarationSpecifier>();
        if (decl.isAbstract())
            specs.add(factory.createAbstract());
        if (decl.isPrivate())
            specs.add(factory.createPrivate());
        if (decl.isProtected())
            specs.add(factory.createProtected());
        if (decl.isPublic())
            specs.add(factory.createPublic());
        if (decl.isFinal())
            specs.add(factory.createAbstract());
        if (decl.isStatic())
            specs.add(factory.createStatic());
        return specs;
    }

    /*
     * add a method to the member set
     */
    private void addMethod(MethodInfo method) {

        MethodDeclaration decl = factory.createMethodDeclaration();
        decl.setDeclarationSpecifiers(makeMethodSpecifiers(method));

        // feature: ignore access functions which should not ne visible on
        // source code level
        String methodName = method.getName();
        if(isInternal(methodName)) 
            return;
        
        String returntype = method.getTypeName();
        returntype = resolveTypeVariable(returntype, method.getTypeParameters());
        TypeReference type = createTypeReference(returntype);
        decl.setTypeReference(type);
        
        decl.setIdentifier(factory.createIdentifier(methodName));

        ASTList<ParameterDeclaration> params = new ASTArrayList<ParameterDeclaration>();
        int index = 1;
        for (String tys : method.getParameterTypeNames()) {
            tys = resolveTypeVariable(tys, method.getTypeParameters());
            type = createTypeReference(tys);
            String name = "arg" + (index++);
            Identifier id = factory.createIdentifier(name);
            params.add(factory.createParameterDeclaration(type, id));
        }
        decl.setParameters(params);

        String[] exceptionsInfo = method.getExceptionsInfo();
        if (exceptionsInfo != null) {
            ASTList<TypeReference> _throws = new ASTArrayList<TypeReference>();

            for (String tys : exceptionsInfo) {
                tys = resolveTypeVariable(tys, method.getTypeParameters());
                type = createTypeReference(tys);
                _throws.add(type);
            }
            decl.setThrown(factory.createThrows(_throws));
        }

        // Body is deliberately set to null in all cases!
        decl.setBody(null);

        memberDecls.add(decl);
    }
    
    /*
     * add a default constructor
     * this is used for enums, it is therefore made private
     */
    private void addDefaultConstructor() {
        Identifier id = factory.createIdentifier(getClassName());
        Private priv = factory.createPrivate();
        ASTList<ParameterDeclaration> params = new ASTArrayList<ParameterDeclaration>();
        ConstructorDeclaration decl = factory.createConstructorDeclaration(priv, id, params, null, null);
        memberDecls.add(decl);
    }
    
    /*
     * add a constructor to the member set. 
     */
    private void addConstructor(ConstructorInfo constr) {
        ConstructorDeclaration decl = factory.createConstructorDeclaration();
        decl.setDeclarationSpecifiers(makeMethodSpecifiers(constr));
        
        decl.setIdentifier(factory.createIdentifier(getClassName()));
        
        ASTList<ParameterDeclaration> params = new ASTArrayList<ParameterDeclaration>();
        int index = 1;
        TypeReference type;
        
        for (String tys : constr.getParameterTypeNames()) {
            tys = resolveTypeVariable(tys, constr.getTypeParameters());
            // filter out those constructors with a Classname$1 argument
            // that are only introduced for technical reasons
            if(ClassFileDeclarationBuilder.isAnononymous(tys))
                return;
            type = createTypeReference(tys);
            String name = "arg" + (index++);
            Identifier id = factory.createIdentifier(name);
            params.add(factory.createParameterDeclaration(type, id));
        }
        decl.setParameters(params);

        String[] exceptionsInfo = constr.getExceptionsInfo();
        if (exceptionsInfo != null) {
            ASTList<TypeReference> _throws = new ASTArrayList<TypeReference>();

            for (String tys : exceptionsInfo) {
                type = createTypeReference(tys);
                _throws.add(type);
            }
            decl.setThrown(factory.createThrows(_throws));
        }

        // Body is deliberately set to null in all cases!
        decl.setBody(null);

        memberDecls.add(decl);
    }

    
    /*
     * Helper:
     * see also recoder.kit,PackageKit
     */
    private PackageReference makePackageReference(String name) {
        PackageReference result = null;
        int i, j = -1;
        do {
            i = j + 1;
            j = name.indexOf(".", i);
            String token = (j > i) ? name.substring(i, j) : name.substring(i);
            result = factory.createPackageReference(result, factory.createIdentifier(token));
        } while (j > i);
        return result;
    }
    
    /*
     * in the presence of (generic) type parameters
     * replace every type parameter by its first boundary.
     * There are three sources for type parameters:
     * <ol>
     * <li> type parameters in the classfile
     * <li> type parameters from the enclosing classfiles (gathered in getAllTypeParameters)
     * <li> additional parameters (from constr/methdo decl)
     * </ol>
     */
    private String resolveTypeVariable(String typename, List<? extends TypeParameter> additionalTypeParameters) {
        
        int dim = 0;
        while(typename.endsWith("[]")) {
            typename = typename.substring(0, typename.length() - 2);
            dim++;
        }
        
        for (TypeParameter tp : getAllTypeParameters()) {
            if (typename.equals(tp.getName())) {
                return tp.getBoundName(0);
            }
        }
        if(additionalTypeParameters != null) {
            for (TypeParameter tp : additionalTypeParameters) {
                if (typename.equals(tp.getName())) {
                    return tp.getBoundName(0);
                }
            }   
        }
        for (int i = 0; i < dim; i++) {
            typename += "[]";
        }
        
        return typename;
    }
    
    /*
     * gather all type parameters. The ones of this class and potentially 
     * the ones of an enclosing class. Store the result for later calls
     *  
     * @return a possibly cached list of all type parameters used in
     * this class, not null.
     */
    private List<TypeParameterInfo> getAllTypeParameters() {
        if(typeParameters == null) {
            typeParameters = new ArrayList<TypeParameterInfo>(0);
            typeParameters.addAll(classFile.getTypeParameters());
            if(isInnerClass() || isAnonymousClass()) {
                ClassFileDeclarationBuilder encl = manager.getBuilder(getEnclosingName());
                typeParameters.addAll(encl.getAllTypeParameters());
            }
        }
        return typeParameters;
    }


    /*
     * Helper: create a type reference to an arbitrary type.
     * $ are introduced instead of . if identifier are numbers or
     * start with digits.
     * This is not used at the moment - but might be interesting if 
     * anonymous classes are mapped, too.
     */
    private TypeReference createTypeReference(String typename) {
       
        int dimension = 0;
        while(typename.endsWith("[]")) {
            dimension ++;
            typename = typename.substring(0, typename.length()-2);
        }
        
        // rare occasion where an anonymous class is used as a marker.
        // happens only in methods not present in source code.
        // bugfix: treatment to the situations:
        //    CN.1.1  -->  CN$1$1
        //    CN.1.D  -->  CD$1.D  etc.
        String[] parts = typename.split("(\\.|\\$)");
        typename = parts[0];
        for (int i = 1; i < parts.length; i++) {
            if(startsWithADigit(parts[i])) {
                typename += "$" + parts[i];
            } else {
                typename += "." + parts[i];
            }
        }
        
        TypeReference tyref = TypeKit.createTypeReference(factory, typename);
        tyref.setDimensions(dimension);
        return tyref;
    }
    
    
    /*
     * is this a reference to an anonymous class?
     * The argument must contain "." not "$"
     */
    private static boolean isAnononymous(String tys) {
        return startsWithADigit(tys.substring(tys.lastIndexOf('.')+1));
    }
    
    /*
     * check if a string starts with a decimal digit.
     * @param string to check
     * @return true iff string denotes a decimal number
     */
    private static boolean startsWithADigit(String string) {
        char c0 = string.charAt(0);
        return c0 >= '0' && c0 <= '9';
    }
    
    /*
     * an internal name contains an '$'
     */
    private static boolean isInternal(String name) {
        return name.contains("$");
    }

    @Override
    public String toString() {
        return "ClassFileDeclarationBuilder[" + getFullClassname() + "]";
    }

    /**
     * compare to class file declaration builders.
     * comparison is performed upon the full classnames
     */
    @Override    
    public int compareTo(ClassFileDeclarationBuilder o) {
        return getFullClassname().compareTo(o.getFullClassname());
    }
    
    @Override    
    public boolean equals(Object o) {
	if(! (o instanceof ClassFileDeclarationBuilder)) {
	    return false;
	}
	return compareTo((ClassFileDeclarationBuilder) o) == 0;
    }
    
    @Override
    public int hashCode() {
	return getFullClassname().hashCode();
    }
}
