// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext;

import java.io.*;

import recoder.*;
import recoder.abstraction.ClassType;
import recoder.bytecode.*;
import recoder.io.DataLocation;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.reference.*;
import recoder.kit.TypeKit;
import recoder.list.generic.*;
import recoder.service.*;
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
 * TODO This builder *cannot* handle anonymous and inner classes yet.
 * 
 * @author MU
 */

public class ClassFileDeclarationBuilder {

    // used to create elements
    private ProgramFactory factory;

    // unit under investigation
    private ClassFile classFile;

    // the result
    private CompilationUnit compilationUnit;

    // the class or interface declaration
    private TypeDeclaration typeDecl;

    // this is the location for error messages etc.
    private DataLocation dataLocation;

    // the member to the declaration are collected here
    private ASTList<MemberDeclaration> memberDecls;

    /**
     * create a new ClassDeclaration builder. The builder can be used to create a
     * ClassDeclaration for a single class file.
     * 
     * @param programFactory the factory to be used to create elements
     * @param classFile class file to be investigated
     */
    public ClassFileDeclarationBuilder(ProgramFactory programFactory, ClassFile classFile) {
        super();
        this.factory = programFactory;
        this.classFile = classFile;
    }

    
    /**
     * get the class name stored in the class file. May contain '$' for inner or
     * anonymous classes
     * 
     * @return the physical name of the class in the class file
     */
    public String getClassname() {
        return classFile.getPhysicalName();
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
            for (ConstructorInfo constr : classFile.getConstructorInfos()) {
                addConstructor(constr);
            }
            for (FieldInfo field : classFile.getFieldInfos()) {
                addField(field);
            }
            for (MethodInfo method : classFile.getMethodInfos()) {
                addMethod(method);
            }
            typeDecl.setMembers(memberDecls);
        }
        return typeDecl;
    }
    
    /**
     * set the location to be stored in the compilation unit, mainly for
     * error reporting.
     * 
     * @param dataLocation, location to be set or null 
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
        String physicalName = classFile.getPhysicalName();
        if(physicalName.contains("$")) {
            String trailing = physicalName.substring(physicalName.indexOf('$') + 1);
            return !isNumber(trailing);
        }
        return false;
    }
    
    
   


    /* TODO DOC*/
    public void attachToEnclosingCompilationUnit(ServiceConfiguration sc) {
        if(!isInnerClass())
            throw new IllegalStateException("only inner classes can be attached to enclosing classes");
        
        NameInfo nameInfo = sc.getNameInfo();
        String enclosingName = getEnclosingName();
        ClassType ct = nameInfo.getClassType(enclosingName);
        
        if(!(ct instanceof TypeDeclaration)) {
            throw new IllegalStateException(enclosingName + " is not present as source code; but:" + ct);
        } else {
            TypeDeclaration td = (TypeDeclaration) ct;
            ASTList<MemberDeclaration> members = td.getMembers();
            assert members != null : "ClassDeclaration with null members!";
            TypeDeclaration childtd = makeTypeDeclaration();
            members.add(childtd);
            sc.getChangeHistory().attached(childtd);
        }
    }
    
    private String getEnclosingName() {
        if(!isInnerClass())
            throw new IllegalStateException("only inner classes have an enclosing class");
        String physicalName = classFile.getPhysicalName();
        return physicalName.substring(0, physicalName.indexOf('$'));
    }

    /**
     * make a stub class declaration for a fully qualified type reference.
     * 
     * If the type reference stands for an array, the trailing [] are
     * discarded first.
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
    public static CompilationUnit makeEmptyClassFile(
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
        cuString += "class " + fullClassName.substring(lastdot+1) + " { }";

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
        } else {
            throw new ConvertException("Only Interfaces and classes are allowed as byte code files");
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
        String fullName = classFile.getFullName();
        int lastDot = fullName.lastIndexOf('.');
        String className = fullName.substring(lastDot + 1);
        typeDecl.setIdentifier(factory.createIdentifier(className));

        ASTArrayList<DeclarationSpecifier> specs = new ASTArrayList<DeclarationSpecifier>();

        if (classFile.isAbstract())
            specs.add(factory.createAbstract());
        if (classFile.isPublic())
            specs.add(factory.createPublic());
        if (classFile.isFinal())
            specs.add(factory.createFinal());
        if (classFile.isStrictFp())
            specs.add(factory.createStrictFp());

        typeDecl.setDeclarationSpecifiers(specs);
    }

    /*
     * set super types, and implemented (or extended) interfaces
     */    
    private void setInheritance() {
        
        // do not inherit Object from itself!
        if("java.lang.Object".equals(classFile.getPhysicalName()))
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
        } else {
            InterfaceDeclaration intfDecl = (InterfaceDeclaration) typeDecl;
            ASTList<TypeReference> implList = new ASTArrayList<TypeReference>();
            for (String intf : interfaceNames) {
                implList.add(createTypeReference(intf));
            }
            if(implList.size() > 0)
                intfDecl.setExtendedTypes(factory.createExtends(implList));
        }
        
        if(superClassName != null) {
            
        }
        
    }

    /*
     * add a package specification if not in the default package.
     */
    private void setPackage() {
        String fullName = classFile.getFullName();
        int packIndex = fullName.lastIndexOf('.');
        // default package: job done
        if (packIndex < 0)
            return;
        String packName = fullName.substring(0, packIndex);
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
            specs.add(factory.createAbstract());
        return specs;
    }

    /*
     * Add a field to the member list
     * TODO compile time constants.
     */
    private void addField(FieldInfo field) {

        String typename = field.getTypeName();
        TypeReference type = createTypeReference(typename);
        Identifier id = factory.createIdentifier(field.getName());
        FieldDeclaration decl = factory.createFieldDeclaration(type, id);

        decl.setDeclarationSpecifiers(makeFieldSpecifiers(field));
        
        memberDecls.add(decl);

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
        return specs;
    }

    /*
     * add a method to the member set
     */
    private void addMethod(MethodInfo method) {
        MethodDeclaration decl = factory.createMethodDeclaration();
        decl.setDeclarationSpecifiers(makeMethodSpecifiers(method));

        String returntype = method.getTypeName();
        TypeReference type = createTypeReference(returntype);
        decl.setTypeReference(type);

        decl.setIdentifier(factory.createIdentifier(method.getName()));

        ASTList<ParameterDeclaration> params = new ASTArrayList<ParameterDeclaration>();
        int index = 1;
        for (String tys : method.getParameterTypeNames()) {
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
     * add a constructor to the member set. 
     */
    private void addConstructor(ConstructorInfo constr) {
        ConstructorDeclaration decl = factory.createConstructorDeclaration();
        decl.setDeclarationSpecifiers(makeMethodSpecifiers(constr));
        
        decl.setIdentifier(factory.createIdentifier(constr.getName()));
        
        ASTList<ParameterDeclaration> params = new ASTArrayList<ParameterDeclaration>();
        int index = 1;
        TypeReference type;
        
        for (String tys : constr.getParameterTypeNames()) {
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
     * Helper: create a type reference to an arbitrary type.
     */
    private TypeReference createTypeReference(String typename) {
        int dimension = 0;
        while(typename.endsWith("[]")) {
            dimension ++;
            typename = typename.substring(0, typename.length()-2);
        }
        TypeReference tyref = TypeKit.createTypeReference(factory, typename);
        tyref.setDimensions(dimension);
        return tyref;
    }
    
    /**
     * check if a string denotes a decimal number
     * @param string
     * @return true iff string denotes a decimal number
     */
    private boolean isNumber(String string) {
        try {
            Integer.parseInt(string);
            return true;
        } catch (NumberFormatException e) {
            return false;
        }
    }

    /**
     * Open a class file, transcribe it to a class Declaration and output the stub.
     * 
     * @param args the first element is taken as a file name to a class file
     * @throws Exception if I/O fails
     */
    public static void main(String args[]) throws Exception {
        CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        ByteCodeParser bcp = new ByteCodeParser();
        ClassFile cf = bcp.parseClassFile(new FileInputStream(args[0]));

        ClassFileDeclarationBuilder b = new ClassFileDeclarationBuilder(sc.getProgramFactory(), cf);
        b.setDataLocation(new URLDataLocation(new File(args[0]).toURL()));
        CompilationUnit cu = b.makeCompilationUnit();
        System.out.println(cu.toSource());
    }

}
