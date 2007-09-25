// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.tree;


import java.util.NoSuchElementException;

import de.uka.ilkd.asmkey.logic.*;
import de.uka.ilkd.asmkey.logic.sort.EnumeratedSort;
import de.uka.ilkd.asmkey.logic.sort.GenericSort;
import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.asmkey.parser.ast.*;
import de.uka.ilkd.asmkey.parser.env.*;
import de.uka.ilkd.asmkey.util.graph.GraphException;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.NonCollectionSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;



/** Class to parse all kinds of declarations.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public abstract class DeclarationParser implements AstDeclarationVisitor, AstSchemaTypeVisitor {

    /** Create and return an array of sorts. The i-th entry references
     * the sort identified by id[i]. */
    private static Sort[] getSorts(SortEnvironment env, AstType[] types)
	throws ParserException {
        Sort[] sorts = new Sort[types.length];
        for (int i = 0; i < sorts.length; ++i) {
	    if (types[i].getSort().getText().equals("asm rule")) {
		sorts[i] = PrimitiveSort.ASMRULE;  
	    } else {
		sorts[i] = EnvironmentUtil.getSort(env, types[i]);
	    }
        }
        return sorts;
    }

    private static FormalParameter[] getFormalParameters(SortEnvironment env, AstParameter[] params)
    throws ParserException {
	FormalParameter[] fps = new FormalParameter[params.length];
	Sort sort;
	for (int i = 0; i < fps.length; ++i) {
	    if (params[i].getSort().getSort().getText().equals("asm rule")) {
		sort = PrimitiveSort.ASMRULE;  
	    } else {
		sort = EnvironmentUtil.getSort(env, params[i].getSort());
	    }
	    fps[i] = FormalParameter.createFormalParameter
		(params[i].getId().getText(), sort);
	}
	return fps;
    }


    /** The environment that is used for parsing and to which new
     * declarations are added. */
    protected final DeclarationEnvironment env;

    /** The name of the DeclarationEnvironment env
     * can be "" if the name is null
     */
    protected final Name name;

    /** Hash map for beyond second pass for the derived operators
     */
    protected final DerivedGraph deriveds;

    /** Temporary stores the identifier of the declaration. This
     * simplifies access to this identifier. */
    private transient Identifier id;


    /** Create a declaration parser that uses the given declaration
     * environment. All new declarations are added to this
     * environment. */
    public DeclarationParser(DeclarationEnvironment env) {
        this.env = env;
	this.name = env.name();
	this.deriveds = new DerivedGraph();
    }


    /** Parse an array of declarations and add them to the
     * environment. it is abstract and will be implemented in 
     * a DeclarationParserFactory.
     * @see DeclarationParserFactory
     * @see TestFirstPass 
     */
    public abstract void parse(AstUnitDeclarations decls) throws ParserException;

    /** Parse a single pass declaration and add it to the environment. */
    protected void parseSingle(AstSinglePassDeclaration decl) throws ParserException {
        id = decl.getId();
        decl.accept(this);
        id = null;
    }

    /** Parse a multi pass declaration and add it to the environment. */
    protected void parseFirstPass(AstMultiPassDeclaration decl) throws ParserException {
        id = decl.getId();
        decl.acceptFirstPass(this);
        id = null;
    }

    /** Second parse of a multi declaration */
    protected void parseSecondPass(AstMultiPassDeclaration decl) throws ParserException {
	id = decl.getId();
	decl.acceptSecondPass(this);
	id = null;
    }
    
    /** To create fully qualified names from the identifier
     */
    private Name createFullyQualified(Identifier id) {
	return createFullyQualified(id.getText());
    }

    private Name createFullyQualified(String id) {
	return new Name(name.toString() + "." + id);
    }

    private Name[] createFullyQualified(Identifier[] ids) {
	Name[] names = new Name[ids.length];
	for (int i = 0; i< ids.length; i++) {
	    names[i] = createFullyQualified(ids[i]);
	}
	return names;
    }

    /* --- Interface: DeclarationVisitor --- */

    public void visitPrimitiveSort(boolean isGenericSort)
	throws ParserException {        
        try {
	    Sort newSort;
	    Name name = createFullyQualified(id);
	    if (isGenericSort) {
		newSort = new GenericSort(name);
	    } else {
		newSort = PrimitiveSort.builtInSort(name);
		if (newSort == null) {
		    newSort = new PrimitiveSort(name);
		}
	    }
	    env.addSort(newSort);
	    if (newSort instanceof NonCollectionSort) {
		NonCollectionSort ns = (NonCollectionSort) newSort;
		//env.addSort(ns.getSetSort());
		//env.addSort(ns.getBagSort()); we need no bags
		env.addSort(ns.getSequenceSort());
	    }
        } catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

    public void visitEnumeratedSort(Identifier[] consts_id)
    throws ParserException {
	try {
	    EnumeratedSort newSort;
	    Function[] consts;
	    Taclet[] taclets;
	    Name name = createFullyQualified(id);
	    newSort = (EnumeratedSort) EnumeratedSort.builtInSort(name);
	    if (newSort == null) {
		newSort = new EnumeratedSort(createFullyQualified(id),
					     createFullyQualified(consts_id));
	    }
	    env.addSort(newSort);
	    consts = newSort.getConstants();
	    for(int i=0; i<consts.length; i++) {
		env.addOperator(consts[i]);
	    }
	    taclets = newSort.getTaclets();
	    for(int i=0; i<taclets.length; i++) {
		env.addTaclet(taclets[i]);
	    }
	} catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), id.getLocation());
	}
    }

    public void visitSchemaVariable(final AstSchemaType type)
	throws ParserException {
	type.accept(this);
    }

    public void visitPredicate(AstType[] args)
    throws ParserException {
        addFunction("Predicate", id, args, Sort.FORMULA, false);
    }

    public void visitDerivedPredicateFirstPass(AstParameter[] params) 
    throws ParserException {
	addDerivedFunctionFirstPass("Predicate", id, params, Sort.FORMULA);
    }

    public void visitDerivedPredicateSecondPass(AstTerm formula) 
    throws ParserException {
	addBodySecondPass("Function", id, formula);
    }

    public void visitFunction(AstType[] args, AstType ret, boolean dynamic)
    throws ParserException {
            Sort retSort = EnvironmentUtil.getSort(env, ret);
            addFunction("Function", id, args, retSort, dynamic);
    }

    public void visitDerivedFunctionFirstPass(AstParameter[] params, AstType ret)
    throws ParserException {
	Sort retSort = EnvironmentUtil.getSort(env, ret);
	addDerivedFunctionFirstPass("Function", id, params, retSort);
    } 

    public void visitDerivedFunctionSecondPass(AstTerm body)
    throws ParserException {
	addBodySecondPass("Function", id, body);
    }

    private void addFunction(String text, Identifier id, AstType[] args,
			     Sort retSort, boolean dynamic)
	throws ParserException {
        try {
            Sort[] sorts = args == null ? new Sort[] {}
                : getSorts(env, args);
            Name name = createFullyQualified(id);
	    Function f;
	    if (dynamic) {
		/* if a function is dynamic, we add TWO function: the function
		 * itself and its timed 
		 * version. 
		 */
		f = new NonRigidFunction(name, retSort, sorts);
		env.addOperator(f);
		
		Name timedName;
		Function timedF;
		Sort[] timedSorts;
		
		timedName = createFullyQualified(id.getText() + "_");
		timedSorts = new Sort[sorts.length + 1];
		for (int i = 1; i <= sorts.length; i++) {
		    timedSorts[i] = sorts[i-1];
		}
		timedSorts[0] = env.getSort(new Name("int"));
		timedF = new TimedNonRigidFunction(timedName, retSort, timedSorts);
		env.addOperator(timedF);
	    } else {
		f = new RigidFunction(name, retSort, sorts);
		env.addOperator(f);
	    }
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

    private void addDerivedFunctionFirstPass(String text, Identifier id, AstParameter[] params,
					     Sort retSort) 
    throws ParserException {
	try {
	    FormalParameter[] args = params == null ?  new FormalParameter[] {}
		: getFormalParameters(env, params);
	    Name name = createFullyQualified(id);
	    env.addOperator(new ParsingDerivedFunction(name, retSort, args, id.getLocation()));
	} catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), id.getLocation());
	}
    }

    private void addBodySecondPass(String text, Identifier id, AstTerm body) 
	throws ParserException {
	try {
	    Name name=createFullyQualified(id);
	    ParsingDerivedFunction func;
	    try {
		func = (ParsingDerivedFunction) env.getOperator(name);
	    } catch (ClassCastException e) {
		throw new ParserException
		    ("The function " + name + " was not registred as ParsingDerivedFunction",
		     id.getLocation()); 
	    }
	    CallEnvironment callEnv = new CallEnvironment
		(env, func.formalParameters());
	    func.setBody(TermParser.parseTerm(callEnv, body), body.getLocation()); 
	    deriveds.add(func);
	} catch (EnvironmentException ee) {
 	    throw new ParserException(ee.getMessage(), id.getLocation());
	} catch (GraphException ge) {
	    throw new ParserException(ge.getMessage(), id.getLocation());
	}
    }


    public void visitTaclet(AstTaclet taclet) throws ParserException {
        TacletDeclarationParser.parse(env, id, createFullyQualified(id), taclet);
    }

    public void visitAbstractAsmRule()
    throws ParserException {
	try {
            AsmRule p = new AsmRule.AbstractAsmRule(createFullyQualified(id));
            env.addRule(p);
	}
	catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
	}
    }

    public void visitNamedRuleFirstPass(AstParameter[] params)
    throws ParserException {
        try {
            FormalParameter[] fps = getFormalParameters(env, params);
            AsmRule p = new AsmRule.DerivedAsmRule(createFullyQualified(id), fps, null, false);
            env.addRule(p);
	}
	catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
	}
    }

    public void visitNamedRuleSecondPass(AstAsmRule prog) 
    throws ParserException {
	try {
	    Name name=createFullyQualified(id);
	    AsmRule.DerivedAsmRule rule;
	    try {
		rule = (AsmRule.DerivedAsmRule) env.getRule(name);
	    } catch (ClassCastException e) {
		throw new ParserException
		    ("The rule " + name + " was not registred as AsmRule",
		     id.getLocation()); 
	    }
	    CallEnvironment callEnv = new CallEnvironment
		(env, rule.formalParameters());
	    rule.setBody(TermParser.parseAsmRule(callEnv, prog), prog.getLocation()); 
	    deriveds.add(rule);
	} catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), id.getLocation());
	} catch (GraphException ge) {
	    throw new ParserException(ge.getMessage(), id.getLocation());
	}
    }

    public void visitLemma(AstParameter[] params, AstTerm phi)
    throws ParserException {
	try {
	    Term term;
	    AsmLemma lemma;
	   
	    term = TermParser.parseTerm(env, phi);
	    if (term.sort() == Sort.FORMULA) {
		lemma = new AsmLemma(createFullyQualified(id), term);
		env.addLemma(lemma);
	    } else {
		throw new ParserException("A lemma requires a formula.", id.getLocation());
	    }
	} catch(EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), id.getLocation());
	}
    }

    public void visitRuleSet() throws ParserException {
	try {
	    env.addRuleSet(new RuleSet(createFullyQualified(id.getText())));
	} catch(EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), id.getLocation());
	}
    }

    public void visitMetaOperator() throws ParserException {
	try {
	    env.addMetaOperator
		(AsmMetaOperator.getMetaOperator(createFullyQualified(id.getText())));
	} catch (NoSuchElementException e) {
	    throw new ParserException(e.getMessage(), id.getLocation());
	} catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), id.getLocation());
	}
    }


    /* --- SchemaVariableDeclarationVisitor */

    public void visitPrimitive(PrimitiveSchemaType t, boolean rigid, Location location)
	throws ParserException {    
	try {
	    if (t == PrimitiveSchemaType.FORMULA) {
		env.addSchemaVariable(SchemaVariableFactory.createFormulaSV
				      (createFullyQualified(id), false, rigid));
	    } else if (t == PrimitiveSchemaType.ASMRULE) {
		env.addSchemaVariable(SchemaVariableFactory.createTermSV
				      (createFullyQualified(id), PrimitiveSort.ASMRULE, false));
	    } else {
		throw new ParserException("unknown primitive schema type",
					  location);
	    }
	} catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), location);
	}
    }
    
    public void visitComposed(AstType sortId, boolean rigid, Location location) throws ParserException {
	try {
	    Sort sort = EnvironmentUtil.getSort(env, sortId);
	    env.addSchemaVariable
		(SchemaVariableFactory.createTermSV
		 (createFullyQualified(id), sort, false, rigid, false));
	} catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), location);
	}
    }
    
    public void visitVariable(AstType sortId, Location location) throws ParserException {
	try {
	    Sort sort = EnvironmentUtil.getSort(env, sortId);
	    env.addSchemaVariable
		(SchemaVariableFactory.createVariableSV
		 (createFullyQualified(id), sort, false));
	} catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), location);
	}
    }
    
    public void visitDepending(AstType sortId, Location location) throws ParserException {
	try {
	    Sort sort = EnvironmentUtil.getSort(env, sortId);
	    env.addSchemaVariable
		(SchemaVariableFactory.createSkolemTermSV
		 (createFullyQualified(id), sort, false));
	} catch (EnvironmentException ee) {
	    throw new ParserException(ee.getMessage(), location);
	}
    }
    
}
