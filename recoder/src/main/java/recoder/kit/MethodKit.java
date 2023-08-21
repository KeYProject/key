/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import recoder.ProgramFactory;
import recoder.abstraction.*;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Abstract;
import recoder.java.declaration.modifier.VisibilityModifier;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.expression.operator.New;
import recoder.java.reference.*;
import recoder.java.statement.Return;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.*;
import recoder.util.Debug;
import recoder.util.Queue;

/**
 * This class implements auxiliary method related operations.
 *
 * @author UA
 * @author AL
 * @author RN
 * @author AM (getAllRelatedMethods)
 */
public class MethodKit {

    private MethodKit() {
        super();
    }

    /**
     * Creates a list of argument expressions from a parameter container. This method is usefull for
     * creating wrapper methods since the actual parameters are taken from the given parameter list.
     */
    public static ASTList<Expression> createArguments(ParameterContainer p) {
        int c = p.getParameterDeclarationCount();
        ASTList<Expression> res = new ASTArrayList<>(c);
        for (int i = 0; i < c; i += 1) {
            res.add(VariableKit.createVariableReference(p.getParameterDeclarationAt(i)));
        }
        return res;
    }

    /**
     * Makes a method reference to the method declaration with the same actual argument names as in
     * the declaration. For constructing adapters. Don't use a reference prefix.
     * <p>
     * The parent role of the result is valid.
     */
    public static MethodReference createMethodReference(MethodDeclaration decl) {
        ProgramFactory factory = decl.getFactory();
        return factory.createMethodReference(factory.createIdentifier(decl.getName()),
            createArguments(decl));
    }

    /**
     * makes a method reference to the method declaration with the same actual argument names as in
     * the declaration. For constructing adapters. Use a reference prefix.
     * <p>
     * The parent role of the result is valid.
     */
    public static MethodReference createMethodReference(ReferencePrefix prefix,
            MethodDeclaration decl) {
        ProgramFactory factory = decl.getFactory();
        return factory.createMethodReference(prefix, factory.createIdentifier(decl.getName()),
            createArguments(decl));
    }

    /**
     * Make a new allocation corresponding to the constructor declaration with the same actual
     * argument names as in the declaration.
     */
    public static New createNew(ConstructorDeclaration decl) {
        return decl.getFactory().createNew(null, TypeKit.createTypeReference(decl),
            createArguments(decl));
    }

    /**
     * Make an new abstract method declaration from a concrete one. The given method may not be
     * static. If the method is for an interface, any existing redundant abstract modifier is
     * removed, otherwise its existance is ensured; any visibility modifier is removed - this
     * changes the visibility to public.
     *
     * @param decl the MethodDeclaration to be made abstract
     * @param forInterface boolean indicating if the abstract method is for an interface
     * @return the abstract method declaration
     * @deprecated not tested
     */
    @Deprecated
    public static MethodDeclaration createAbstractMethodDeclaration(MethodDeclaration decl,
            boolean forInterface) {
        ProgramFactory factory = decl.getFactory();
        // create some prototypes
        if (decl.isStatic()) {
            throw new IllegalArgumentException("A static method cannot made abstract!");
        }
        StatementBlock body = decl.getBody();
        decl.setBody(null); // not necessary to clone this.
        MethodDeclaration res = decl.deepClone();
        decl.setBody(body);
        Abstract anAbstract = factory.createAbstract();
        int abstractPos;
        ASTList<DeclarationSpecifier> modList = res.getDeclarationSpecifiers();
        if (modList == null) {
            abstractPos = -1;
        } else {
            abstractPos = modList.indexOf(anAbstract);
        }
        VisibilityModifier vismod = res.getVisibilityModifier();
        if (forInterface) {
            // interfaces should not have an abstract
            if (abstractPos >= 0) {
                modList.remove(abstractPos);
            }
            // interfaces should not have a visibility modifier
            if (vismod != null) {
                modList.remove(vismod);
            }
        } else {
            if (abstractPos < 0) {
                // we need an abstract here
                if (modList == null) {
                    res.setDeclarationSpecifiers(
                        modList = new ASTArrayList<>(1));
                }
                modList.add((vismod == null) ? 0 : 1, anAbstract);
            } else {
                return res; // already there
            }
        }
        return res;
    }

    /**
     * Create a simple adapter method for a method declaration. If the method is
     * <p>
     * m(int i, int i2) { ..}
     * <p>
     * the created method is
     * <p>
     * m(int i, int i2) { delegatingObject.m(i,i2); }
     */
    public static MethodDeclaration createAdapterMethod(ReferencePrefix delegationObject,
            MethodDeclaration method) {
        MethodDeclaration clone = method.deepClone();
        clone.setComments(
            new ASTArrayList<>(new DocComment("/** generated by createAdapterMethod */")));

        // empty the clone method and add the to the member list
        clone.setBody(new StatementBlock(new ASTArrayList<>()));

        // add the adapter statements
        MethodReference call = createMethodReference(delegationObject, method);
        clone.getBody().getBody().add(call);
        return clone;
    }

    /**
     * Creates a packer class for parameter list of a method. This Packer class contains one
     * constructor which tuples all parameters of the method into an object. Works on AST elements.
     *
     * @param packerClassName the String with the name of the packer class
     * @param parameters the list of {@link ParameterDeclaration}s for the packer class to wrap
     * @return the class declaration of the packed class
     * @deprecated needs severe rework (AL)
     */
    @Deprecated
    public static ClassDeclaration createPackerClass(String packerClassName,
            List<ParameterDeclaration> parameters) {
        StatementBlock statements;
        ASTList<MemberDeclaration> memberList;
        ClassDeclaration packClass;
        ParameterDeclaration parameter;
        ConstructorDeclaration constructor;

        Debug.printlno("debugPackifier", "creating packer class " + packerClassName);
        ProgramFactory factory = JavaProgramFactory.getInstance();

        // Turn parameter list into member list of the Packer class.
        memberList = new ASTArrayList<>();
        for (ParameterDeclaration declaration : parameters) {
            parameter = declaration;

            // Don't destroy the original DeclarationSpecifier list, copy it.
            ASTList<DeclarationSpecifier> modifierlist = new ASTArrayList<>();
            // Parameter may not be public.
            // All fields must be set to public.
            modifierlist.add(factory.createPublic());

            // XX normalize parameter decls //
            Identifier fieldName =
                factory.createIdentifier(parameter.getVariables().get(0).getName());
            // Stupid, Name is no parameter to createFieldDeclaration// XX must
            // be done for all params
            FieldDeclaration fd =
                factory.createFieldDeclaration(parameter.getTypeReference(), fieldName);
            fd.setDeclarationSpecifiers(modifierlist);
            memberList.add(fd);
        }

        // Add a constructor to the Packer class.
        ASTList<DeclarationSpecifier> modifierlist = new ASTArrayList<>();
        modifierlist.add(factory.createPublic());
        constructor = factory.createConstructorDeclaration(factory.createPublic(),
            factory.createIdentifier(packerClassName),
            // (ParameterDeclarationMutableList) parameters
            null, null, statements = factory.createStatementBlock());

        // Create the initialization statements for all parameters
        // in the constructor.
        for (ParameterDeclaration parameterDeclaration : parameters) {
            parameter = parameterDeclaration;
            String paramString = parameter.getVariables().get(0).getName(); // XX
            // must
            // be
            // done
            // for all params
            // XX should be an assign??
            FieldReference fieldRef = factory.createFieldReference(factory.createThisReference(),
                factory.createIdentifier(paramString));
            CopyAssignment assign = factory.createCopyAssignment(fieldRef,
                factory.createVariableReference(factory.createIdentifier(paramString)));
            statements.getBody().add(assign);
        }
        memberList.add(constructor);

        // Create the Packer class itself.
        modifierlist = new ASTArrayList<>();
        modifierlist.add(factory.createPublic());
        // should we not add public anymore since the help class is within the
        // modified class?
        packClass =
            factory.createClassDeclaration(
                modifierlist, factory.createIdentifier(packerClassName), factory
                        .createExtends(
                            factory.createTypeReference(
                                factory.createPackageReference(
                                    factory.createPackageReference(
                                        factory.createIdentifier("java")),
                                    factory.createIdentifier("lang")),
                                factory.createIdentifier("Object"))),
                factory.createImplements(), memberList);

        Debug.printlno("debugPackifier", "created packer " + packerClassName);
        return packClass;
    }

    /**
     * Query that tries to identify getter methods for the given field within the class declaration
     * of the given field. The criteria used are quite conservative and detect obvious cases of
     * "getters" only. A method is regarded a getter if it is defined in the class of the field, has
     * a return type wider than the type of the field (or matching if they are primitive) and has a
     * return statement as last top level statement of the method body referring to the field.
     *
     * @param si the source info service to be used.
     * @param f the field to find a getter for.
     * @return the list of getters; may be empty if there are no getters that match the criteria in
     *         the class.
     */
    public static List<MethodDeclaration> getGetters(SourceInfo si, FieldSpecification f) {
        Debug.assertNonnull(si, f);
        List<MethodDeclaration> res = new ArrayList<>();
        TypeDeclaration tdecl = (TypeDeclaration) f.getContainingClassType();
        if (tdecl instanceof InterfaceDeclaration) {
            return res;
        }
        List<MemberDeclaration> mems = tdecl.getMembers();
        if (mems == null) {
            return res;
        }
        Type fieldType = si.getType(f);
        for (int i = mems.size() - 1; i >= 0; i -= 1) {
            MemberDeclaration md = mems.get(i);
            if (!(md instanceof MethodDeclaration)) {
                continue;
            }
            MethodDeclaration m = (MethodDeclaration) md;
            if (fieldType instanceof PrimitiveType) {
                if (m.getReturnType() != fieldType) {
                    continue;
                }
            } else {
                if (!si.isWidening(fieldType, m.getReturnType())) {
                    continue;
                }
            }
            StatementBlock body = m.getBody();
            if (body == null) {
                continue;
            }
            List<Statement> statements = body.getBody();
            if (statements == null) {
                continue;
            }
            Statement last = statements.get(statements.size() - 1);
            if (!(last instanceof Return)) {
                continue;
            }
            Expression expr = ((Return) last).getExpression();
            if (!(expr instanceof FieldReference)) {
                continue;
            }
            FieldReference fr = (FieldReference) expr;
            if (si.getField(fr) == f) {
                res.add(m);
            }
        }
        return res;
    }

    /**
     * Transformation that renames a method and all known references to it. The new name should not
     * hide another method.
     *
     * @param ch the change history (may be <CODE>null</CODE>).
     * @param xr the cross referencer service.
     * @param method the method declaration to be renamed; may neither be <CODE>
     *                null</CODE> nor a constructor declaration.
     * @param newName the new name for the method; may not be <CODE>null</CODE> and must denote a
     *        valid identifier name.
     * @return <CODE>true</CODE>, if a rename has been necessary, <CODE>
     * false</CODE> otherwise.
     * @deprecated replaced by recoder.kit.transformation.RenameMethod
     */
    @Deprecated
    public static boolean rename(ChangeHistory ch, CrossReferenceSourceInfo xr,
            MethodDeclaration method, String newName) {
        Debug.assertNonnull(xr, method, newName);
        Debug.assertNonnull(method.getName());
        Debug.assertBoolean(!(method instanceof ConstructorDeclaration));
        if (!newName.equals(method.getName())) {
            List<MemberReference> refs = xr.getReferences(method);
            MiscKit.rename(ch, method, newName);
            for (int i = refs.size() - 1; i >= 0; i -= 1) {
                MiscKit.rename(ch, (MethodReference) refs.get(i), newName);
            }
            return true;
        }
        return false;
    }

    /**
     * Query that returns a list of methods that the given method directly overwrites or implements.
     * A method that is multiply inherited (from interfaces) occurs multiple times, accordingly.
     *
     * @param m a method.
     * @return a list of methods that are overwritten or implemented by <CODE>m
     * </CODE>.
     */
    public static List<Method> getRedefinedMethods(Method m) {
        Debug.assertNonnull(m);
        if (m instanceof Constructor) {
            return new ArrayList<>(0);
        }
        ClassType ct = m.getContainingClassType();
        String mname = m.getName();
        List<Type> msig = m.getSignature();
        List<Method> result = new ArrayList<>();
        List<? extends ClassType> supers = ct.getSupertypes();
        for (int i = supers.size() - 1; i >= 0; i -= 1) {
            List<? extends Method> meths = supers.get(i).getAllMethods();
            for (int j = meths.size() - 1; j >= 0; j -= 1) {
                Method m2 = meths.get(j);
                if (m2.getName().equals(mname) && m2.getSignature().equals(msig)) {
                    result.add(m2);
                }
            }
        }
        return result;
    }

    /**
     * Query that returns a list of methods that redefine or implement the given method.
     *
     * @param xr the cross referencer service to use.
     * @param m a method.
     * @return a list of methods that redefine or implement <CODE>m</CODE>.
     */
    public static List<Method> getRedefiningMethods(CrossReferenceSourceInfo xr, Method m) {
        Debug.assertNonnull(m);
        if (m instanceof Constructor) {
            return new ArrayList<>(0);
        }
        ClassType ct = m.getContainingClassType();
        String mname = m.getName();
        List<Type> msig = m.getSignature();
        List<Method> result = new ArrayList<>();
        List<? extends ClassType> subs = xr.getAllSubtypes(ct);
        for (int i = subs.size() - 1; i >= 0; i -= 1) {
            List<? extends Method> meths = subs.get(i).getMethods();
            for (int j = meths.size() - 1; j >= 0; j -= 1) {
                Method m2 = meths.get(j);
                if (m2.getName().equals(mname) && m2.getSignature().equals(msig)) {
                    result.add(m2);
                }
            }
        }
        return result;
    }

    /**
     * Updating query that checks if the given method is a main method.
     *
     * @param ni the NameInfo service to use.
     * @param m the method to check.
     * @return <CODE>true</CODE> if the given method has the form "public static void main(String[]
     *         ...)", <CODE>false</CODE> otherwise.
     */
    public static boolean isMain(NameInfo ni, Method m) {
        if (!m.isPublic()) {
            return false;
        }
        if (!m.isStatic()) {
            return false;
        }
        if (!m.getName().equals("main")) {
            return false;
        }
        if (m.getReturnType() != null) {
            return false;
        }
        List<Type> list = m.getSignature();
        if (list.size() != 1) {
            return false;
        }
        // we do not have to create an array type, as this would have been
        // done by the getSignature call already.
        return list.get(0) == ni.getArrayType(ni.getJavaLangString());
    }

    /**
     * Updating query that checks if the given method is one of the serialization methods
     * <CODE>writeObject</CODE>,<CODE>readObject
     * </CODE>,<CODE>writeReplace</CODE>,<CODE>readResolve</CODE>.
     *
     * @param ni the NameInfo service to use.
     * @param m the method to check.
     * @return <CODE>true</CODE> if the given method is one of the serialization methods,
     *         <CODE>false</CODE> otherwise.
     */
    public static boolean isSerializationMethod(NameInfo ni, Method m) {
        if (m.getName().equals("writeObject") && m.isPrivate() && m.getReturnType() == null
                && m.getSignature().size() == 1
                && m.getSignature().get(0) == ni.getClassType("java.io.ObjectOutputStream")) {
            return true;
        }
        if (m.getName().equals("readObject") && m.isPrivate() && m.getReturnType() == null
                && m.getSignature().size() == 1
                && m.getSignature().get(0) == ni.getClassType("java.io.ObjectInputStream")) {
            return true;
        }
        if (m.getName().equals("writeReplace") && m.getReturnType() == ni.getJavaLangObject()
                && m.getSignature().isEmpty()) {
            return true;
        }
        return m.getName().equals("readResolve") && m.getReturnType() == ni.getJavaLangObject()
                && m.getSignature().isEmpty();
    }

    /**
     * Returns a deep clone of the header of the given declaration; the body of the result is
     * <CODE>null</CODE>.
     *
     * @param md the method declaration to clone the header from.
     * @return a new method declaration sharing the header with the given one.
     * @see recoder.java.SourceElement#deepClone()
     */
    public static MethodDeclaration cloneHeader(MethodDeclaration md) {
        StatementBlock body = md.getBody();
        md.setBody(null);
        MethodDeclaration result = md.deepClone();
        md.setBody(body);
        return result;
    }

    /**
     * Query returning a method locally defined in the given type with the given name and signature.
     *
     * @param type the class type the method might be defined in.
     * @param name the name of the method.
     * @param signature the signature of the method.
     * @return the method as defined in the class type, or <CODE>null</CODE> if there is no match.
     */
    public static Method getDefinedMethod(ClassType type, String name, List<Type> signature) {
        List<? extends Method> methods = type.getMethods();
        for (int j = methods.size() - 1; j >= 0; j -= 1) {
            Method m = methods.get(j);
            if (name.equals(m.getName()) && signature.equals(m.getSignature())) {
                return m;
            }
        }
        return null;
    }

    /**
     * Query returning the methods which a method in the given class with the given name and
     * signature would redefine. If there are several candidates from independent interfaces, the
     * bottom-most ones are reported. If there is a version defined in a super class, it will be the
     * first entry in the list (position 0).
     *
     * @param ni the name info service to use.
     * @param base the class type which would contain the redefining method.
     * @param name the name of the possibly redefining method.
     * @param signature the signature of the possibly redefining method.
     * @return a list of methods that are directly redefined by a method with the given name and
     *         signature; the first entry is the method inherited from a class, if any.
     */
    public static List<Method> getRedefinedMethods(NameInfo ni, ClassType base, String name,
            List<Type> signature) {
        List<? extends ClassType> supers = base.getSupertypes();
        List<Method> result = new ArrayList<>();
        boolean hasClass = false;
        for (ClassType ct : supers) {
            Method m = getDefinedMethod(ct, name, signature);
            if (m != null) {
                if (!ct.isInterface()) {
                    result.add(0, m);
                    hasClass = true;
                } else {
                    result.add(m);
                }
            }
        }
        if (!hasClass) {
            ClassType ct = base;
            do {
                ct = TypeKit.getSuperClass(ni, ct);
                Method m = getDefinedMethod(ct, name, signature);
                if (m != null) {
                    result.add(0, m);
                    break;
                }
            } while (ct != ni.getJavaLangObject());
        }
        return result;
    }

    /**
     * Query that finds out problems if one method redefines another one. The redefining method does
     * not have to actually redefine the other method, the query just assumes it does. The query
     * also assumes that names and signatures of the methods will match and that both have the same
     * class. The query will not check any contents of the redefining method, e.g. to see if private
     * members of the super class are accessed.
     *
     * @param pmi a program model info to use.
     * @param redefined the method to be redefined.
     * @param redefining the method that is / would be redefining.
     * @return a problem report, one of the following:
     *         <UL>
     *         <LI>FinalOverwrite, if the redefined method is final;
     *         <LI>DifferentReturnTypeOverwrite, if the redefining method has a different return
     *         type;
     *         <LI>MorePrivateOverwrite, if the redefining method is more private;
     *         <LI>NonStaticOverwrite, if the redefined method is static but the redefining is not
     *         (if both are static, no problem is reported, even though no real redefinition is
     *         taking place);
     *         <LI>UncoveredExceptionsOverwrite, if the redefined method is less exceptional;
     *         <LI><CODE>null</CODE>, otherwise.
     *         </UL>
     */
    public static Problem checkMethodRedefinition(ProgramModelInfo pmi, Method redefined,
            Method redefining) {

        if (redefining instanceof Constructor) {
            return null;
        }
        if (redefined.isFinal() || redefined.getContainingClassType().isFinal()) {
            return new FinalOverwrite(redefined);
        }
        if (redefined.getReturnType() != redefining.getReturnType()) {
            return new DifferentReturnTypeOverwrite(redefined);
        }
        if (TypeKit.isLessVisible(redefining, redefined)) {
            return new MorePrivateOverwrite(redefined);
        }
        if (!redefining.isStatic() && redefined.isStatic()) {
            return new NonStaticOverwrite(redefined);
        }
        // check exceptions
        List<? extends ClassType> exceptions = redefining.getExceptions();
        if (exceptions != null) {
            List<? extends ClassType> redefinedex = redefined.getExceptions();
            if (redefinedex == null || !TypeKit.isCovered(pmi, redefinedex, exceptions)) {
                return new UncoveredExceptionsOverwrite(redefined);
            }
        }
        return null;
    }

    /**
     * Query that finds out problems before inserting a new method declaration.
     *
     * @param ni the name info to use.
     * @param si the source info to use.
     * @param context the future context of the method.
     * @param candidate the method declaration that might be inserted.
     * @return a problem report, one of the following:
     *         <UL>
     *         <LI>IllegalInterfaceMember, if the context is an interface and the candidate is not a
     *         valid member;
     *         <LI>IllegalName, if the name is a keyword;
     *         <LI>NameConflict, if the candidate is a constructor and its name does not match the
     *         type name;
     *         <LI>NameConflict, if there is a method in the context with the same name and
     *         signature;
     *         <LI>FinalOverwrite, if there is a redefined method that is final;
     *         <LI>DifferentReturnTypeOverwrite, if there is a redefined method with different
     *         return type;
     *         <LI>MorePrivateOverwrite, if there is a redefined method that is more public;
     *         <LI>NonStaticOverwrite, if there is a redefined method that is static;
     *         <LI>UncoveredExceptionsOverwrite, if there is a redefined method that is less
     *         exceptional;
     *         <LI><CODE>null</CODE>, otherwise.
     *         </UL>
     */
    public static Problem checkMethodDeclaration(NameInfo ni, SourceInfo si,
            TypeDeclaration context, MethodDeclaration candidate) {

        if (context instanceof InterfaceDeclaration) {
            if (!TypeKit.isValidInterfaceMember(candidate)) {
                return new IllegalInterfaceMember(candidate);
            }
        }
        if (candidate instanceof Constructor) {
            if (!candidate.getName().equals(context.getName())) {
                return new NameConflict(context);
            }
        } else {
            if (Naming.isKeyword(candidate.getName())) {
                return new IllegalName(candidate);
            }
        }
        List<MemberDeclaration> members = context.getMembers();
        String name = candidate.getName();
        List<Type> signature = candidate.getSignature();
        if (members != null) {
            for (int i = members.size() - 1; i >= 0; i -= 1) {
                MemberDeclaration md = members.get(i);
                if (md instanceof MethodDeclaration) {
                    MethodDeclaration m = (MethodDeclaration) md;
                    if (m.getName().equals(name) && m.getSignature().equals(signature)) {
                        return new NameConflict(m);
                    }
                }
            }
        }

        if (candidate instanceof Constructor) {
            return null;
        }
        List<Method> redefined = MethodKit.getRedefinedMethods(ni, context, name, signature);
        for (Method method : redefined) {
            Problem problem = checkMethodRedefinition(si, method, candidate);
            if (problem != null) {
                return problem;
            }
        }
        return null;
    }

    /**
     * Query that retrieves all references to a given method that are contained within the given
     * tree. The specified flag defines the strategy to use: either the cross reference information
     * is filtered, or the cross reference information is collected from the tree. The filtering
     * mode is faster if the tree contains more nodes than there are global references to the given
     * method.
     *
     * @param xr the cross referencer to use.
     * @param m a method.
     * @param root the root of an arbitrary syntax tree.
     * @param scanTree flag indicating the search strategy; if <CODE>true</CODE>, local cross
     *        reference information is build, otherwise the global cross reference information is
     *        filtered.
     * @return the list of references to the given method in the given tree, can be empty but not
     *         <CODE>null</CODE>.
     * @since 0.63
     */
    public static List<MemberReference> getReferences(CrossReferenceSourceInfo xr, Method m,
            NonTerminalProgramElement root, boolean scanTree) {
        Debug.assertNonnull(xr, m, root);
        List<MemberReference> result = new ArrayList<>();
        if (scanTree) {
            TreeWalker tw = new TreeWalker(root);
            if (m instanceof Constructor) {
                while (tw.next(ConstructorReference.class)) {
                    ConstructorReference cr = (ConstructorReference) tw.getProgramElement();
                    if (xr.getConstructor(cr) == m) {
                        result.add(cr);
                    }
                }
            } else {
                while (tw.next(MethodReference.class)) {
                    MethodReference mr = (MethodReference) tw.getProgramElement();
                    if (xr.getMethod(mr) == m) {
                        result.add(mr);
                    }
                }
            }
        } else {
            List<MemberReference> refs = xr.getReferences(m);
            for (MemberReference mr : refs) {
                if (MiscKit.contains(root, mr)) {
                    result.add(mr);
                }
            }
        }
        return result;
    }

    /**
     * Query that returns a list of methods would redefine, implement or are overriden or
     * implemented each other starting from method <CODE>
     * methodName</CODE> in <CODE>type</CODE> with specified <CODE>signature
     * </CODE>. The method does not have to actually exist in <CODE>type
     * </CODE> the query just assumes it does.
     *
     * @param xrsi the cross referencer service to use.
     * @param type the type which contain method.
     * @param methodName name of the method.
     * @param signature method signature.
     * @return a list of related methods.
     * @since 0.72
     */
    public static List<Method> getAllRelatedMethods(CrossReferenceSourceInfo xrsi, ClassType type,
            String methodName, List<Type> signature) {
        Debug.assertNonnull(xrsi, type, methodName, signature);

        RelatedMethodsHelper rmh = new RelatedMethodsHelper(xrsi, type, methodName, signature);
        return rmh.findRelatedMethods();
    }

    /**
     * Query that returns a list of methods that redefine, implement or are overriden or implemented
     * each other starting from method <CODE>method
     * </CODE>. There are some cases where related methods might be outside of descendants or
     * ascendants of type containing <CODE>method</CODE>. For instance,
     * <CODE>Collection.size()</CODE> is related to <CODE>
     * Dictionary.size()</CODE>, because <CODE>Hashtable</CODE> extends <CODE>Dictionary</CODE> and
     * indirectly implements <CODE>Collection
     * </CODE>.
     *
     * @param xrsi the cross referencer service to use.
     * @param method a method.
     * @return a list of related methods including <CODE>method</CODE>.
     * @since 0.72
     */
    public static List<Method> getAllRelatedMethods(CrossReferenceSourceInfo xrsi, Method method) {
        Debug.assertNonnull(method);
        return getAllRelatedMethods(xrsi, method.getContainingClassType(), method.getName(),
            method.getSignature());
    }

    public static List<Method> getAllRelatedMethods(NameInfo ni, CrossReferenceSourceInfo xrsi,
            ClassType type, String methodName, List<Type> signature) {
        Set<ClassType> visited = new HashSet<>();
        Queue q = new Queue();
        q.enqueue(type);
        visited.add(type);
        List<Method> result = new ArrayList<>();
        while (!q.isEmpty()) {
            type = (ClassType) q.dequeue();
            Method m = getDefinedMethod(type, methodName, signature);
            if (m != null) {
                result.add(m);
            }
            List<Method> redefined = getRedefinedMethods(ni, type, methodName, signature);
            for (int i = redefined.size() - 1; i >= 0; i--) {
                ClassType ct = redefined.get(i).getContainingClassType();
                if (visited.add(ct)) {
                    q.enqueue(ct);
                }
            }
            if (m != null || !redefined.isEmpty()) {
                List<? extends ClassType> types = xrsi.getSubtypes(type);
                for (int i = types.size() - 1; i >= 0; i--) {
                    ClassType ct = types.get(i);
                    if (visited.add(ct)) {
                        q.enqueue(ct);
                    }
                }
            }
        }
        return result;
    }

    /**
     * @author AM
     */
    private static class RelatedMethodsHelper {

        private final List<Method> methods = new ArrayList<>();

        private final Set<ClassType> searchedUp = new HashSet<>();

        private final Set<ClassType> searchedDown = new HashSet<>();

        private final CrossReferenceSourceInfo xrsi;

        private final ClassType starting_type;

        private final String methodName;

        private final List<Type> signature;

        public RelatedMethodsHelper(CrossReferenceSourceInfo xrsi, ClassType type,
                String methodName, List<Type> signature) {
            this.xrsi = xrsi;
            this.methodName = methodName;
            this.signature = signature;
            this.starting_type = type;
        }

        public List<Method> findRelatedMethods() {
            addMethodsFromSubTypes(starting_type);
            return methods;
        }

        private void addMethodsFromSubTypes(ClassType type) {
            if (!searchedDown.add(type)) {
                return;
            }
            List<? extends ClassType> subTypes = xrsi.getSubtypes(type);
            if (subTypes.isEmpty()) {
                // leaf class
                addMethodsFromSuperTypes(type);
            } else {
                for (int i = subTypes.size() - 1; i >= 0; i--) {
                    ClassType child = subTypes.get(i);
                    addMethodsFromSubTypes(child);
                }
            }
        }

        private void addMethodsFromSuperTypes(ClassType type) {
            if (!searchedUp.add(type)) {
                return;
            }
            Method m = getDefinedMethod(type, methodName, signature);
            if (m != null) {
                methods.add(m);
                addMethodsFromSubTypes(type);
            }
            List<? extends ClassType> superTypes = type.getSupertypes();
            for (int i = superTypes.size() - 1; i >= 0; i--) {
                ClassType parent = superTypes.get(i);
                addMethodsFromSuperTypes(parent);
            }
        }
    }

}
