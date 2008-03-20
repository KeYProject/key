package de.uka.ilkd.key.java.recoderext;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.Reader;
import java.io.Writer;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.bytecode.ByteCodeParser;
import recoder.bytecode.ClassFile;
import recoder.bytecode.ConstructorInfo;
import recoder.bytecode.FieldInfo;
import recoder.bytecode.MethodInfo;
import recoder.io.DataLocation;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.PackageSpecification;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.PackageReference;
import recoder.java.reference.TypeReference;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

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
 * This builder *cannot* handle anonymous and inner classes yet.
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

    // this is the location for errormessages etc.
    private DataLocation dataLocation;

    // the member to the declaration are collected here
    private ASTList<MemberDeclaration> memberDecls;

    /**
     * create a new ClassDeclaration builder. The builder can be used to create a
     * ClassDeclaration for a single class file.
     * 
     * @param programFactory the factory to be used to create elements
     * @param classFile classfile to be investigated
     */
    public ClassFileDeclarationBuilder(ProgramFactory programFactory, ClassFile classFile) {
        super();
        this.factory = programFactory;
        this.classFile = classFile;
    }

    /**
     * retrieve the compilation unit for the classfile under consideration.
     * 
     * The second and following calls will return the cached value of the 
     * inital calculation.
     * 
     * @return a compilation unit correspoding to the class file.
     */
    public CompilationUnit makeCompilationUnit() {
        if (compilationUnit == null) {
            compilationUnit = new CompilationUnit();
            setPackage();
            createTypeDeclaration();
            setNameAndMods();
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
            compilationUnit.makeAllParentRolesValid();
            compilationUnit.setDataLocation(dataLocation);
        }
        return compilationUnit;
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
            throw new RuntimeException("Only Interfaces and classes are allowed as byte code files");
        }
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
     * TODO are these all the possiblie mods?
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
            String name = "arg" + index;
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
