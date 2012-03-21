// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package recoder.service;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;

import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.convenience.Naming;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.Import;
import recoder.java.ProgramElement;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.StatementContainer;
import recoder.java.TypeScope;
import recoder.java.VariableScope;
import recoder.java.declaration.*;
import recoder.java.reference.TypeReference;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Case;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;
import recoder.service.DefaultCrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.service.UnresolvedReferenceException;
import de.uka.ilkd.key.java.recoderext.ClassFileDeclarationBuilder;
import de.uka.ilkd.key.java.recoderext.adt.*;
import de.uka.ilkd.key.java.recoderext.*;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.SpecDataLocation;


public class KeYCrossReferenceSourceInfo
    extends DefaultCrossReferenceSourceInfo {

    private HashMap<String, recoder.java.declaration.VariableSpecification>  names2vars = null;

    
    public KeYCrossReferenceSourceInfo(ServiceConfiguration config) {
	super(config);
    }

    public void setNames2Vars(HashMap<String, recoder.java.declaration.VariableSpecification> names2vars){
	this.names2vars = names2vars;
    }

    /**
       Called by the service configuration indicating that all services
       are known. Services may now start communicating or linking among
       their configuration partners. The service configuration can be
       memorized if it has not been passed in by a constructor already.
       @param cfg the service configuration this services has been assigned to.
     */
    public void initialize(ServiceConfiguration cfg) {
	super.initialize(cfg);
	cfg.getChangeHistory().
	    removeChangeHistoryListener(this);
	cfg.getChangeHistory().addChangeHistoryListener(this);
	
	//HEAP
	name2primitiveType.put("\\locset", new PrimitiveType("\\locset", this));
	name2primitiveType.put("\\seq", new PrimitiveType("\\seq", this));
	
	// JML's primitive types
	name2primitiveType.put("\\bigint", new PrimitiveType("\\bigint", this));
	name2primitiveType.put("\\real", new PrimitiveType("\\real", this));
    }

    /**
	Returns the class type that contains the given program element.
	@param  context a program element.
	@return the type to which the given program element belongs
	(may be <CODE>null</CODE>).
    */
    public ClassType getContainingClassType(ProgramElement context){
	if (context instanceof TypeDeclaration) {
	    context = context.getASTParent();
	}
	do {
	    if (context instanceof ClassType) {
		return (ClassType)context;
	    }else if(context instanceof MethodCallStatement){
		return (ClassType) getType(((MethodCallStatement) context).
					      getExecutionContext()
					      .getTypeReference());
	    }
	    context = context.getASTParent();
	} while (context != null);
	return null;
    }


    public void modelChanged(ChangeHistoryEvent event) {
	List<TreeChange> changes = new ArrayList<TreeChange>();
	changes.addAll(event.getChanges());
	super.modelChanged(event);

	for (TreeChange change : changes) {
	    if (change instanceof AttachChange) {
		ProgramElement pe = change.getCompilationUnit();
		if (pe instanceof TypeDeclarationContainer) {
		    TypeDeclarationContainer tdc = (TypeDeclarationContainer) pe;
		    for (int i = 0; i<tdc.getTypeDeclarationCount(); i++) {
		        ClassType ct = tdc.getTypeDeclarationAt(i);
		        for (ClassType superType : ct.getSupertypes()) {
		            registerSubtype(ct, superType);
		        }
		    }
		}
	    }
	}
    }

    void registerSubtype(ClassType c1, ClassType c2) {

	try {
	    super.registerSubtype(c1, c2);
	} catch (IllegalAccessError iae) {
	    // eclipse uses different classloaders and they cause an exception here
	    // TODO: package new recoder library with protected registerSubtype
	    // and delete the exception handling code below
	    eclipseWorkaroundMethodAccess(c1, c2);
	}
	
	
	
    }

    // Woraround for eclipse as we need to access a package private method from the superclass
    // even this class is logically in the same package, eclipse uses different classloaders
    // and will not allow this trick
    // TODO: package new recoder library with protected registerSubtype
    // and delete the exception handling code below
    private void eclipseWorkaroundMethodAccess(ClassType c1, ClassType c2) {
	try {
	    Method m = DefaultProgramModelInfo.class.getDeclaredMethod("registerSubtype", ClassType.class, ClassType.class);
	    m.setAccessible(true);
	    m.invoke(this, c1, c2);
	} catch (IllegalAccessException e) {
	    throw (IllegalAccessError)new IllegalAccessError().initCause(e);
	} catch (InvocationTargetException e) {
	    throw (IllegalAccessError)new IllegalAccessError().initCause(e);
	} catch (SecurityException e) {
	    throw (IllegalAccessError)new IllegalAccessError().initCause(e);
	} catch (NoSuchMethodException e) {
	    throw (IllegalAccessError)new IllegalAccessError().initCause(e);
	}
    }

    public Variable getVariable(String name, ProgramElement context) {
        updateModel();
        // look for the next variable scope equals to or parent of context
        ProgramElement pe = context;

        // Enum constants:
        // 2 cases:
        //   1) its an original enum constant (see DefaultSourceInfo)
        //   or
        //   2) its an already transformed enum class constant
        //
        // In the KeY gui, however, the references will always be qualified
        // like in "EnumName.ConstantName"

        // 1)
        if ((context instanceof VariableReference || context instanceof UncollatedReferenceQualifier)
                && context.getASTParent() instanceof Case
                && getType(((Case)context.getASTParent()).getParent().getExpression()) instanceof EnumDeclaration) {
            /* is it an enum constant? Possible iff:
             * 1) parent is "case" and
             * 2) switch-selector is an enum type (that way, the selector specifies the scope!)
             */
            EnumConstantSpecification ecs = (EnumConstantSpecification)((EnumDeclaration)getType(((Case)context.getASTParent()).getParent().getExpression())).getVariableInScope(name);
            if (ecs != null) {
                return ecs;
            } else {
                // must not resolve! qualifying enum constant in case-statements is forbidden!
                return null;
            }
        }

        // 2)
        if ((context instanceof VariableReference || context instanceof UncollatedReferenceQualifier)
                && context.getASTParent() instanceof Case
                && getType(((Case)context.getASTParent()).getParent().getExpression()) instanceof EnumClassDeclaration) {
            /* is it an enum class constant (after transformation)? Possible iff:
             * 1) parent is "case" and
             * 2) switch-selector is an enum type (that way, the selector specifies the scope!)
             */
            EnumClassDeclaration ecd = ((EnumClassDeclaration)getType(((Case)context.getASTParent()).getParent().getExpression()));
            VariableSpecification vs = ecd.getVariableInScope(name);
            if (vs != null) {
                return vs;
            } else {
                // must not resolve! qualifying enum constant in case-statements is forbidden!
                return null;
            }
        }

        while (pe != null
                && !(pe instanceof VariableScope)
                && !((pe instanceof MethodCallStatement)
                        && !(context instanceof ExecutionContext) && !(context
                        .equals(((MethodCallStatement) pe).getResultVariable())))) {
            context = pe;
            pe = pe.getASTParent();

        }
        if (pe == null) {
            // a null scope can happen if we try to find a variable
            // speculatively (for URQ resolution)
            return null;
        }
        if (pe instanceof MethodCallStatement
                && !(context instanceof ExecutionContext)
                && !(context.equals(((MethodCallStatement) pe)
                        .getResultVariable()))) {
            pe = getTypeDeclaration((ClassType) getType(((MethodCallStatement) pe)
                    .getExecutionContext().getTypeReference()));
        }
        VariableScope scope = (VariableScope) pe;
        Variable result;
        do {
            result = scope.getVariableInScope(name);
            if (result != null) {
                // must double check this result - rare cases of confusion
                // involving field references before a local variable of the
                // same name has been specified
                if (scope instanceof StatementBlock) {
                    StatementContainer cont = (StatementBlock) scope;
                    // we need the topmost var-scope including context,
                    // or context itself if the found scope is the topmost one
                    VariableDeclaration def = ((VariableSpecification) result)
                            .getParent();
                    for (int i = 0; true; i += 1) {
                        Statement s = cont.getStatementAt(i);
                        if (s == def) {
                            // Debug.log(">>> Not ignored: " +
                            // Format.toString("%c \"%s\" @%p", result)
                            // + " for context " +
                            // Format.toString("@%p", context));

                            // stop if definition comes first
                            break;
                        }
                        if (s == context) {
                            // tricky: reference before definition - must
                            // ignore the definition :(

                            // Debug.log(">>> Ignored: " +
                            // Format.toString("%c \"%s\" @%p", result)
                            // + " for context " +
                            // Format.toString("@%p", context));

                            result = null;
                            break;
                        }
                    }
                }
                if (result != null) {
                    // leave _now_
                    break;
                }
            }
            if (scope instanceof TypeDeclaration) {
                result = getInheritedField(name, (TypeDeclaration) scope);
                if (result != null) {
                    break;
                }
                // might want to check for ambiguity of outer class fields!!!
            }
            pe = scope.getASTParent();
            while (pe != null
                    && !(pe instanceof VariableScope)
                    && !((pe instanceof MethodCallStatement) && !(context instanceof ExecutionContext))) {
                context = pe; // proceed the context
                pe = pe.getASTParent();
            }
            if (pe instanceof MethodCallStatement
                    && !(context instanceof ExecutionContext)
                    && !(context.equals(((MethodCallStatement) pe)
                            .getResultVariable()))) {
                pe = getTypeDeclaration((ClassType) getType(((MethodCallStatement) pe)
                        .getExecutionContext().getTypeReference()));
            }
            scope = (VariableScope) pe;
        } while (scope != null);
        // we were at the compilation unit scope, leave for good now
        if (result == null && names2vars != null) {
            return names2vars.get(name);
        }
        return result;
    }

    /**
     * Tries to find a type with the given name using the given program element
     * as context. Useful to check for name clashes when introducing a new
     * identifier. Neither name nor context may be <CODE>null</CODE>.
     *
     * This method is identical to
     * {@link DefaultCrossReferenceSourceInfo#getType(String, ProgramElement)}
     * but it uses <code>pe = redirectScopeNesting(pe);</code> instead of
     * <code>s.getASTParent();</code> in Recoder 0.84.
     *
     * @param name
     *                the name for the type to be looked up; may or may not be
     *                qualified.
     * @param context
     *                a program element defining the lookup context (scope).
     * @return the corresponding type (may be <CODE>null</CODE>).
     */
    public Type getType(String name, ProgramElement context) {

        NameInfo ni = getNameInfo();

        // check primitive types, array types of primitive types,
        // and void --- these happen often
        Type t = name2primitiveType.get(name);
        if (t != null) {
            return t;
        }
        if (name.equals("void")) {
            return null;
        }
        // catch array types
        if (name.endsWith("]")) {
            int px = name.indexOf('[');
            // compute base type
            Type baseType = getType(name.substring(0, px), context);
            if (baseType == null) {
                return null;
            }
            String indexExprs = name.substring(px);
            // the basetype exists now, so fetch a corresponding array type
            // (if there is none, the name info will create one)
            return ni.getType(baseType.getFullName() + indexExprs);
        }

        updateModel();

        // in the very special case that we are asking from the point of
        // view of a supertype reference, we must move to the enclosing unit
        // or parent type
        if (context.getASTParent() instanceof InheritanceSpecification) {
            context = context.getASTParent().getASTParent().getASTParent();
        }

        ProgramElement pe = context;
        while (pe != null && !(pe instanceof TypeScope)) {
            context = pe;
            pe = redirectScopeNesting(pe);
        }
        TypeScope scope = (TypeScope) pe;
        ClassType result = null;

        // do the scope walk
        TypeScope s = scope;
        while (s != null) {
            result = getLocalType(name, s);
            if (result != null) {
                // must double check this result - rare cases of confusion
                // involving type references before a local class of the
                // corresponding name has been specified
                if (s instanceof StatementBlock) {
                    StatementContainer cont = (StatementBlock) s;
                    for (int i = 0; true; i += 1) {
                        Statement stmt = cont.getStatementAt(i);
                        if (stmt == result) {
                            // stop if definition comes first
                            break;
                        }
                        if (stmt == context) {
                            // tricky: reference before definition - must
                            // ignore the definition :(
                            result = null;
                            break;
                        }
                    }
                }
                if (result != null) {
                    // leave _now_
                    break;
                }
            }
            if (s instanceof TypeDeclaration) {
                TypeDeclaration td = (TypeDeclaration) s;
                ClassType newResult = getInheritedType(name, td);

                if (newResult != null) {
                    result = newResult;
                    break;
                }
            }
            scope = s;
            pe = s.getASTParent();
            while (pe != null && !(pe instanceof TypeScope)) {
                context = pe;
                pe = redirectScopeNesting(pe);
            }
            s = (TypeScope) pe;
        }
        if (result != null) {
            return result;
        }        
        
        // now the outer scope is null, so we have arrived at the top
        CompilationUnit cu = (CompilationUnit) scope;

        ASTList<Import> il = cu.getImports();
        if (il != null) {
            // first check type imports
            result = getFromTypeImports(name, il);
        }
        if (result == null) {
            // then check same package
            result = getFromUnitPackage(name, cu);
            if (result == null && il != null) {
                // then check package imports
                result = getFromPackageImports(name, il, cu.getTypeDeclarationAt(0 /* doesn't matter which one to check, since this is important for static imports only */));
            }
        }
        if (result == null) {
            // check global types: if unqualified, attempt "java.lang.<name>":
            // any unqualified local type would have been imported already!
            String defaultName = Naming.dot("java.lang", name);
            result = ni.getClassType(defaultName);
            if (result == null) {
                result = ni.getClassType(name);
            }
        }
        if (result != null) {
            scope.addTypeToScope(result, name); // add it to the CU scope
        }
        return result;
    }

    /**
     * redirects the nesting of scopes when a method-frame occurs
     * @param scope the current scope
     * @return the new scope
     */
    private ProgramElement redirectScopeNesting(ProgramElement scope) {
        if (scope instanceof MethodCallStatement) {
            Type type = getType(((MethodCallStatement) scope)
                    .getExecutionContext().getTypeReference());
            if (!(type instanceof TypeDeclaration)) {
                throw new IllegalStateException("In the source section of"
                        + "method-frame only types for which source code is "
                        + "available are supported.");
            }
            return (TypeDeclaration) getType(((MethodCallStatement) scope)
                    .getExecutionContext().getTypeReference());
        } else if (scope instanceof ExecutionContext
                || (scope.getASTParent() instanceof MethodCallStatement &&
                        scope == ((MethodCallStatement) scope.getASTParent()).
                        getResultVariable())) {
            scope = scope.getASTParent();
        }

        return scope.getASTParent();
    }

    /// -------------- Handling of stub class generation

    /**
     * The mapping from class names to stub compilation units.
     */
    protected Map<String, CompilationUnit> stubClasses = new HashMap<String, CompilationUnit>();

    /**
     *  The flag which decides on the behaviour on undefined classes
     */
    private boolean ignoreUnresolvedClasses = false;

    /**
     * Sets if unresolved classes result in an exception or lead to stubs.
     *
     * If unresolved classes are ignored, we use
     * {@link #registerUnresolvedTypeRef(TypeReference)} to create dummy stubs.
     *
     * @param ignoreUnresolvedClasses
     *                ignore unresolved classes iff true
     */
    public void setIgnoreUnresolvedClasses(boolean ignoreUnresolvedClasses) {
        this.ignoreUnresolvedClasses = ignoreUnresolvedClasses;
        if(ignoreUnresolvedClasses) {
            stubClasses.clear();
        }
    }

    /*
     * overwrite the default behaviour:
     * if the normal lookup fails, generate a stub class, register it
     * and try to look up again. This might fail again, should never.
     *
     * @see recoder.service.DefaultSourceInfo#getType(recoder.java.reference.TypeReference)
     */
    @Override
    public Type getType(TypeReference tr) {
        try {
            return super.getType(tr);
        } catch (ExceptionHandlerException e) {
            if(ignoreUnresolvedClasses && e.getCause() instanceof UnresolvedReferenceException) {
                registerUnresolvedTypeRef(tr);
                return super.getType(tr);
            } else {
                throw e;
            }
        }
    }

    /*
     * make dummy classes for unresolved type references, store newly created classes to
     * stubClasses and register the compilation unit.
     */
    private void registerUnresolvedTypeRef(TypeReference tyref) {
        NameInfo ni = serviceConfiguration.getNameInfo();
        String typeString = Naming.toPathName(tyref);

        // bugfix: The reference might be to an array. Remove the array reference then.
        while(typeString.endsWith("[]"))
            typeString = typeString.substring(0, typeString.length() - 2);

        // look in the already created classes:
        CompilationUnit stub = stubClasses.get(typeString);
        if(stub != null)
            throw new IllegalStateException("try to resolve an unknown type twice");

        recoder.abstraction.Type ty;

        try {
            ty = ni.getType(typeString);
        } catch (UnresolvedReferenceException e) {
            // this is still an unknown type, so set ty = null
            ty = null;
        }
        if(ty == null) {
            if(!typeString.contains("."))
                throw new UnresolvedReferenceException("Type references to undefined classes may only appear if they are fully qualified: " + tyref.toSource(), tyref);

            recoder.java.CompilationUnit cu;
            try {
                cu = ClassFileDeclarationBuilder.makeEmptyClassDeclaration(serviceConfiguration.getProgramFactory(), typeString);
                cu.setDataLocation(new SpecDataLocation("stub", typeString));
            } catch (ParserException e) {
                throw new de.uka.ilkd.key.java.ConvertException(e);
            }

            ChangeHistory changeHistory = serviceConfiguration.getChangeHistory();
            changeHistory.attached(cu);
            changeHistory.updateModel();

            stubClasses.put(typeString, cu);
            Debug.out("Dynamically created class: ", typeString);

            register(cu);

        }
    }

    /**
     * Gets the collection of created stub classes ion their compilation units
     *
     * @return the unmodifiable collection of created compilation units
     */
    public Collection<? extends CompilationUnit> getCreatedStubClasses() {
        return stubClasses.values();
    }

    /**
     * clears the cache for the TypeReference to Type resolution.
     * This is necessary if types are added after model evalutation.
     *
    public void clearTypeRefCache() {
        shit: reference2element.clear();
    }*/
    
    @Override 
    public Type getType(Expression expr) {
	if(expr instanceof EmptySetLiteral
           || expr instanceof Singleton
           || expr instanceof SetUnion
           || expr instanceof AllFields) {
	    return name2primitiveType.get("\\locset");
	} else if(expr instanceof EmptySeqLiteral
                  || expr instanceof SeqSingleton
                  || expr instanceof SeqConcat
                  || expr instanceof SeqSub
                  || expr instanceof SeqReverse) {
        return name2primitiveType.get("\\seq");
	} else if(expr instanceof DLEmbeddedExpression) {
	    // w/o further resolution, a type cannot be determined.
	    // but this does not fail.
	    return getNameInfo().getUnknownType();
	} else if (expr instanceof SeqLength
	        || expr instanceof SeqIndexOf){
	    return name2primitiveType.get("\\bigint");
	    // TODO: handle SeqGet
	} else {
	    return super.getType(expr);
	}
    }
}
