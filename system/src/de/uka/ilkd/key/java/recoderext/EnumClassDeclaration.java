// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext;

import java.util.List;

import recoder.ProgramFactory;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.declaration.*;
import recoder.java.expression.operator.New;
import recoder.java.reference.TypeReference;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * This class is used to describe an enum type by its equivalent class
 * declaration.
 * 
 * The transformation {@link EnumClassBuilder} transform an
 * {@link EnumDeclaration} to an EnumClassDeclaration by
 * <ul>
 * <li>adding static fields for the enum constants
 * <li>adding statements in constructors
 * <li>adding static fields for names and ordinals
 * <li>adding the methods as specified in the JLS 8.9
 * <li>adding "extends Enum" to the ClassDeclaration
 * </ul>
 * 
 * <p>
 * Currently anonymous implementations for constants are not supported as they
 * are anonymous inner classes which are not supported by KeY.
 * 
 * <p>
 * The additional methods are constructed as follows (E is the name of the enum,
 * (e1, ..., en) its constants):
 * 
 * <pre>
 *            public static E[] values() { return new E[] { e1,..., en } };
 *            
 *            public static E valueOf(java.lang.String string) {
 *               for(E e : values()) {
 *                  if(e.name().equals(string))
 *                     return e;
 *               }
 *               throw new IllegalArgumentException();
 *            }
 *            
 *            public java.lang.String name() { return ENUM_NAMES[ordinal()]; }
 * </pre>
 * 
 * <p>
 * Additionally the fields that are enum constants are remembered.
 *  
 * @author mulbrich
 * @since 2006-11-18
 * @version 2006-12-05
 */

public class EnumClassDeclaration extends ClassDeclaration {
    
    /**
     * name of the static variable of the array holding the names of the constants.
     */
    private static final String ENUM_NAMES = "<enumConstantNames>";

    private static final String VALUE_OF_PROTO =
            "public static $E valueOf(String string) { for($E e : values()) { if(e.name().equals(string)) return e; } throw new IllegalArgumentException(); }";
    private static final String VALUES_PROTO =
            "public static $E[] values() { return new $E[] { $consts }; }";
    private static final String NAME_PROTO =
            "public java.lang.String name() { return " + ENUM_NAMES
                    + "[ordinal()]; }";

    /**
     * store the EnumConstantDeclarations here.
     * <b>NB: The AST-parent cannot be set to <i>this</i> because
     * it is not a EnumDeclaration.
     */
    private List<EnumConstantDeclaration> enumConstants;

    public EnumClassDeclaration() {
        super();
        enumConstants = new ASTArrayList<EnumConstantDeclaration>();
    }

    /**
     * make a new wrapping class declaration upon a given enum declaration. Deep
     * copy all things instead of relinking them!
     * 
     * Anonymous inner classes are not supported --> no need for an abstract
     * keyword.
     */

    public EnumClassDeclaration(EnumDeclaration ed) {
        this();

        ProgramFactory f = getFactory();

        //
        // Identifier
        setIdentifier(ed.getIdentifier().deepClone());

        //
        // Declaration Specs.
        ASTList<DeclarationSpecifier> orgDecls = ed.getDeclarationSpecifiers();
        ASTList<DeclarationSpecifier> decls;
        if (orgDecls != null)
            decls = orgDecls.deepClone();
        else
            decls = new ASTArrayList<DeclarationSpecifier>();

        if (!ed.isFinal()) {
            decls.add(f.createFinal());
        }

        //
        // Comments
        if (ed.getComments() != null)
            setComments(ed.getComments().deepClone());

        //
        // Extends
        setExtendedTypes(f.createExtends(TypeKit.createTypeReference(f,
                "java.lang.Enum")));

        //
        // Implements
        Implements implement = ed.getImplementedTypes();
        if (implement != null)
            setImplementedTypes(implement.deepClone());

        //
        // Members
        // - Make internal fields
        // - Change constructors, create fields from constants, copy the rest
        ASTList<MemberDeclaration> members =
                new ASTArrayList<MemberDeclaration>();
        setMembers(members);
        for (MemberDeclaration mem : ed.getMembers()) {
            if (mem instanceof EnumConstantDeclaration) {
                members.add(makeConstantField((EnumConstantDeclaration) mem, ed));
                enumConstants.add((EnumConstantDeclaration) mem.deepClone());
            }  else
                members.add((MemberDeclaration)mem.deepClone());

        }

        //
        // fields needed for construction
        addInternalFields();

        //
        // implicitly defined methods
        addImplicitMethods();

        //
        // set parent roles
        makeAllParentRolesValid();
             
    }

    /*
     * there are three methods that are to be implemented: - values() -
     * valueof(String) - name()
     */
    private void addImplicitMethods() {

        //
        // values
        StringBuilder sb = new StringBuilder();
        for (EnumConstantDeclaration ecd : getEnumConstantDeclarations()) {
            if (sb.length() != 0)
                sb.append(", ");
            sb.append(ecd.getEnumConstantSpecification().getIdentifier().getText());
        }
        String valuesString =
                VALUES_PROTO.replace("$E", getIdentifier().getText());
        valuesString = valuesString.replace("$consts", sb.toString());
        MethodDeclaration values = parseMethodDeclaration(valuesString);

        //
        // valueOf
        MethodDeclaration valueOf =
                parseMethodDeclaration(VALUE_OF_PROTO.replace("$E",
                        getIdentifier().getText()));

        //
        // name
        MethodDeclaration name = parseMethodDeclaration(NAME_PROTO);

        ASTList<MemberDeclaration> members = getMembers();
        members.add(valueOf);
        members.add(values);
        members.add(name);
    }

    /*
     * parse a method declaration given as a string. use the
     * ProofJavaProgramFactory to be able to make implicit identifiers.
     */
    private MethodDeclaration parseMethodDeclaration(String string) {
        try {
            return ProofJavaProgramFactory.getInstance().parseMethodDeclaration(
                    string);
        } catch (Exception ex) {
            throw new RuntimeException(ex);
        }
    }

    /*
     * add the ENUM_NAMES field
     */
    private void addInternalFields() {

        ProgramFactory f = getFactory();

        ASTArrayList<DeclarationSpecifier> dsml =
                new ASTArrayList<DeclarationSpecifier>();
        dsml.add(f.createPrivate());
        dsml.add(f.createStatic());
       
        //       
        // ENUM_NAMES       

        dsml = dsml.deepClone();
        dsml.add(f.createFinal());
        
        Expression init;
        /*
        // use this, once Strings are supported
        ASTList<Expression> nameList = new ASTArrayList<Expression>();
        for (EnumConstantDeclaration edc : getEnumConstantDeclarations()) {
            nameList.add(f.createStringLiteral('"' + edc.getEnumConstantSpecification().getIdentifier().getText() + '"'));
        }
        
        init = f.createArrayInitializer(nameList);
        */

        // String literals are not supported at the moment
        init = f.createNullLiteral();

        TypeReference stringArrayType =
                f.createTypeReference(f.createIdentifier("String"), 1);
        

        FieldDeclaration enumNames =
                f.createFieldDeclaration(dsml.deepClone(), stringArrayType,
                        createIdentifier(ENUM_NAMES), init);

        getMembers().add(enumNames);
    }

    /*
     * depending on whether there is a < in the beginning construct a new
     * ImplicitIdentifier or a normal Identifier
     */
    private static Identifier createIdentifier(String string) {
        if (string.startsWith("<"))
            return new ImplicitIdentifier(string);
        else
            return new Identifier(string);
    }

    /**
     * get all declared enum constants for this enum.
     * return them as a list.
     * 
     * @return a list of the enum constants, not null
     */
    public List<EnumConstantDeclaration> getEnumConstantDeclarations() {
        return enumConstants;
    }

    /*
     * make a constantField out of a EnumConstantDeclaration enum A {a1(args)}
     * ==> ... public static A a1 = new A(args); ...
     * 
     */
    private MemberDeclaration makeConstantField(EnumConstantDeclaration ecd,
            EnumDeclaration ed) {
        ProgramFactory f = getFactory();
        EnumConstantSpecification ecs = ecd.getEnumConstantSpecification();
        ASTList<Expression> args = ecs.getConstructorReference().getArguments();

        ASTArrayList<DeclarationSpecifier> dsml =
                new ASTArrayList<DeclarationSpecifier>();

        //
        // Make Constructorref
        New constrref =
                f.createNew(null,
                        f.createTypeReference(getIdentifier().deepClone()),
                        args);

        //
        // make field
        dsml.add(f.createPublic());
        dsml.add(f.createStatic());
        dsml.add(f.createFinal());
        FieldDeclaration fd =
                f.createFieldDeclaration(dsml,
                        f.createTypeReference(getIdentifier().deepClone()),
                        ecs.getIdentifier().deepClone(), constrref);

        return fd;
    }
    
}
