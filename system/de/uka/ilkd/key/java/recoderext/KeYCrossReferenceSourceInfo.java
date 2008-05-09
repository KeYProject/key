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

import java.util.HashMap;

import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.convenience.Format;
import recoder.convenience.Naming;
import recoder.java.*;
import recoder.java.declaration.InheritanceSpecification;
import recoder.java.declaration.EnumConstantSpecification;
import recoder.java.declaration.EnumDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.VariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.list.generic.ASTList;
import recoder.service.AmbiguousReferenceException;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Case;
import recoder.service.DefaultCrossReferenceSourceInfo;
import recoder.service.NameInfo;


public class KeYCrossReferenceSourceInfo 
    extends DefaultCrossReferenceSourceInfo {

    private HashMap names2vars = null;

    /**
       Strict checking. Does not allow "broken links" during reference
       resolution.
     */
    // never used
    //public static final int STRICT = 0;
    
    /**
       Sloppy checking. Allows "broken links" during reference resolution.
     */
    // never used
    //public static final int SLOPPY = 1;


    public KeYCrossReferenceSourceInfo(ServiceConfiguration config) {
	super(config);	
    }

    public void setNames2Vars(HashMap names2vars){
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
            return (recoder.abstraction.Variable) names2vars.get(name);
        }
        return result;
    }

    /**
     * Tries to find a type with the given name using the given program element
     * as context. Useful to check for name clashes when introducing a new
     * identifier. Neither name nor context may be <CODE>null</CODE>.
     * 
     * @param name
     *            the name for the type to be looked up; may or may not be
     *            qualified.
     * @param context
     *            a program element defining the lookup context (scope).
     * @return the corresponding type (may be <CODE>null</CODE>).
     */
    public Type getType(String name, ProgramElement context) {           
        
        NameInfo ni = getNameInfo();

        // check primitive types, array types of primitive types,
        // and void --- these happen often
        Type t = (Type) name2primitiveType.get(name);
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
                    if (result == null) {
                        result = newResult;
                        break;
                    } else if (result != newResult) {
                        // !!!!!!! Problematic if this is a speculative
                        // question - do we really want to bail out?
                        getErrorHandler().reportError(
                                new AmbiguousReferenceException("Type " + Format.toString("%N", newResult)
                                        + " is an inherited member type that is also defined as outer member type "
                                        + Format.toString("%N", result), null, result, newResult));
                        break;
                    }
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
    
    /**
     * clears the cache for the TypeReference to Type resolution.
     * This is necessary if types are added after model evalutation.
     *
    public void clearTypeRefCache() {
        shit: reference2element.clear();
    }*/
}
