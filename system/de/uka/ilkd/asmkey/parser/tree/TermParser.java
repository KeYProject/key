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


import java.util.List;

import de.uka.ilkd.asmkey.logic.*;
import de.uka.ilkd.asmkey.parser.ast.*;
import de.uka.ilkd.asmkey.parser.ast.Operator;
import de.uka.ilkd.asmkey.parser.env.EnvironmentException;
import de.uka.ilkd.asmkey.parser.env.EnvironmentUtil;
import de.uka.ilkd.asmkey.parser.env.TermEnvironment;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;


/** Class to parse terms and asm rules. This class implements the
 * interfaces {@link de.uka.ilkd.asmkey.parser.ast.AstTermVisitor} and
 * {@link de.uka.ilkd.asmkey.parser.ast.AstAsmRuleVisitor} and
 * therefore contains a lot of functions. Only the functions {@link
 * #parse(AstTerm, List)}, {@link #parse(AstAsmRule, List)} and {@link
 * #parse(AstSequent)} should be called.
 *
 * Because terms have to be parsed recursively and bound logical
 * variables can differ in subterms, the visitor uses the closure
 * argument to pass a list of bound logical variables.
 *
 * SN: we use a AsmTermFactory to parse the special timed terms.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */
public final class TermParser implements AstTermVisitor {
    
    private static final Term[] EMPTY_TERMS = new Term[] {};
    
    /** The environment used for parsing terms. */
    private final TermEnvironment env;
    
    /** Shoft reference to the used term factory. */
    private final AsmTermFactory tf = AsmTermFactory.ASMDEFAULT;
    
    
    /** Create a term parser for the given environment. */
    public TermParser(TermEnvironment env) {
        this.env = env;
    }
    
    
    /* --- terms --- */
    
    /** Parse a term with the bound logic variables. The elements of
     * 'logicVariables' have to be of type {@link LogicVariable}. */
    public Term parse(AstTerm term, ListOfOperator logicVariables) throws ParserException {
	return parse2(term, new ParsingStack(logicVariables));
    }
    
    /** Parses a term recursive. Hint: The method uses a different
     * name, because the signature 'Object' is to general and may be
     * called incidental, if {@link #parse(AstTerm, List)} is
     * wanted. */
    private Term parse2(AstTerm term, ParsingStack stack) throws ParserException {
        return (Term) term.accept(this, stack);
    }
    
    /** Parses and returns an array of terms. Calls {@link
     * #parse2(AstTerm, Object)} fo step, r each element. */
    private Term[] parse2(AstTerm[] terms, ParsingStack stack) throws ParserException {
        Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; ++i) {
            result[i] = parse2(terms[i], stack);
        }
        return result;
    }
    
    /* --- Interface: AstTermVisitor --- */
    
    public Object visitOperatorTerm(ParsingStack closure,
				    AstOperator op, AstTerm[] terms, Location location)
	throws ParserException {
	if (op.getOperator() == Operator.EQUALS) {
	    //assert terms != null && terms.length == 2;
	    return tf.createEqualityTerm(parse2(terms[0], closure),
					 parse2(terms[1], closure));
	} else if (op.getOperator() == Operator.EQV) {
	    //assert terms != null && terms.length == 2;
	    return tf.createJunctorTerm(Op.EQV,
					parse2(terms, closure));
	} else {
	    de.uka.ilkd.key.logic.op.Operator op2 = TermParserUtil.convertOp(env, op);
	    return tf.createTerm(op2, terms == null ? null : parse2(terms, closure),
				 (ArrayOfQuantifiableVariable) null,
				 JavaBlock.EMPTY_JAVABLOCK);
	}
    }

    public Object visitBigTerm(ParsingStack closure,
			       AstOperator op, Identifier sort,
			       Identifier func, Identifier var,
			       AstTerm form)
	throws ParserException {
	if (env.isParsingDerivedFunction()) {
	    BigOperator bigop;
	    NArityFunction f;
	    NArityLogicVariable v;
	    Sort s;
	    Term parsed;
	    
	    try {
		s = env.getSort(sort.name());
	    } catch (EnvironmentException e) {
		throw new ParserException(e.getMessage(), sort.getLocation());
	    }
	    if (s instanceof GenericSort || s == Sort.ANY) { 
		f = new NArityFunction(func.name(), s);
		v = new NArityLogicVariable(var.name(), f);
		closure.push(f);
		closure.push(v);
		
		if (op.getOperator() == Operator.BIGAND) {
		    bigop = BigOperator.bigAnd(func.name(), v, f, s);
		} else if (op.getOperator() == Operator.BIGOR) {
		    bigop = BigOperator.bigOr(func.name(), v, f, s);
		} else {
		    throw new ParserException("The operator " + op.getOperator() +
					      " is not a big operator", op.getLocation());
		}
		parsed = tf.createTerm(bigop, new Term[] { parse2(form, closure) },
				       (ArrayOfQuantifiableVariable) null,
				       JavaBlock.EMPTY_JAVABLOCK);
		closure.pop(f);
		closure.pop(v);
		return parsed;
	    } else {
		throw new ParserException
		    ("The sort " + sort.name() +
		     " is no generic: NArityFunction needs a generic sort " +
		     "or Sort.ANY as return sort",
		     sort.getLocation());
	    }
	} else {
	    throw new ParserException("Big operators may only appear in a body of a derived predicate.",
				      op.getLocation());
	}
    }

    public Object visitQuantifierTerm(ParsingStack closure, AstQuantifier q,
                                      Identifier var, Identifier sort, AstTerm term,
				      Location location) 
	throws ParserException {
	if (sort == null) {
	    // schema variable or narity variable
	    if (closure.contains(var.name())) {
		//narity
		de.uka.ilkd.key.logic.op.Operator v = closure.get(var.name());
		if (v instanceof NArityLogicVariable) {
		    return createQuantifierTerm(q, (NArityLogicVariable) v,
						parse2(term, closure));
		}
	    }
	    //otherwise try schema
	    return createQuantifierTerm
		(q,
		 (SortedSchemaVariable)EnvironmentUtil.getSchemaVariable(env, var),
		 parse2(term, closure));
	} else {
	    LogicVariable v = new LogicVariable(TermParserUtil.toName(var),
						EnvironmentUtil.getSort(env, sort));
	    Term parsed;
	    closure.push(v);
	    parsed = createQuantifierTerm(q, v, parse2(term, closure));
	    closure.pop(v);
	    return parsed;
	}
    }
    
    private Term createQuantifierTerm(AstQuantifier q, QuantifiableVariable v, Term term)
        throws ParserException
    {
        return tf.createQuantifierTerm(TermParserUtil.convertQuantifier(q), v, term);
    }
    
    public Object visitFunctionTerm(ParsingStack closure, Identifier id, AstTerm[] terms,
				    Location location)
	throws ParserException {
	Term[] subs =
	    terms == null
	    ? EMPTY_TERMS
	    : parse2(terms, closure);
	if (terms.length == 0 && NumberParser.isNumber(id.getText())) {
	    /* operator name is a number. */
	    try {
		return NumberParser.parseNumber(env, id.getText());
	    } catch (EnvironmentException ee) {
		throw new ParserException(ee.getMessage(), id.getLocation());
	    }
	} else if (closure.contains(id.name())) {
	    de.uka.ilkd.key.logic.op.Operator op = closure.get(id.name());
	    if (op instanceof LogicVariable) {
		/* operator is a logic (bound) variable */
		if (terms.length != 0) {
		    throw new ParserException("Variable " + id + " can not have parameters.",
					      id.getLocation());
		}
		return tf.createVariableTerm((LogicVariable) op);
	    } else if (op instanceof NArityFunction) {
		if (terms.length == 1) {
		    return tf.createFunctionTerm((NArityFunction)op, parse2(terms[0], closure));
		} else {
		    throw new ParserException("The function " + op.name() + "has arity 1",
					      id.getLocation());
		}
	    } else {
		throw new ParserException("The operator " + op.name() +
					  " is not allowed to be on the stack.",
					  id.getLocation());
	    }
	} else if (env.containsOperator(id.name())) {
	    de.uka.ilkd.key.logic.op.Operator op = EnvironmentUtil.getOperator(env, id);
	    if (op instanceof FormalParameter) {
		/* operator is a formal parameter */
		if (terms.length != 0) {
		    throw new ParserException
			("Formal parameter " + id + " can not have parameters.",
			 id.getLocation());
		}
		return ((FormalParameter) op).createTerm(null, EMPTY_TERMS);
	    } else if (op instanceof Operator2) {
		try {
		    /* Operator2 should be called this way. */
		    return TermParserUtil.
			createTerm((Operator2) op, subs);
		} catch (TermNotValidException e) {
		    return new ParserException(e.getMessage(), id.getLocation());
		}
	    } else {
		try {
		    /* else call term factory */
		    if (terms.length == 0) {
			if (op instanceof TimedNonRigidFunction) {
			    throw new ParserException
				("The timed function" + id +
				 "needs at least one argument.",
				 id.getLocation());
			} else {
			    return tf.createFunctionTerm((Function) op);
			}
		    } else {
			return tf.createFunctionTerm((Function) op, subs);
		    }
		} catch (TermCreationException e) {
		    throw new ParserException(e.getMessage(), id.getLocation());
		}
	    }
	} else if(env.containsMetaOp(id.name())) {
	    /* operator is a meta operator */
	    MetaOperator op = EnvironmentUtil.getMetaOp(env, id);
	    if (op instanceof Operator2) {
		return ((Operator2) op).createTerm(null, subs);
	    } else {
		return tf.createMetaTerm(op, subs);
	    }
	} else if (env.containsSchemaVariable(id.name())){
	    /* operator is a schema variable */
	    if (terms.length != 0) {
		throw new ParserException("Variable " + id + " can not have parameters.",
					  id.getLocation());
	    }
	    return tf.createVariableTerm(EnvironmentUtil.getSchemaVariable(env, id));
	} else {
	    throw new ParserException("The identifier " + id + " corresponds to no operators.",
				      id.getLocation());
	}
    }

    public Object visitSubstitutionTerm(ParsingStack closure, Identifier var,
                                        Identifier sort, AstTerm subst, AstTerm term,
					boolean waryEx, boolean waryAll, Location location)
    throws ParserException {
	SubstOp op;
	/*if (waryEx) {
	  op = Op.WARY_SUBST_EX;
	  } else if (waryAll) {
	  op = Op.WARY_SUBST_ALL;
	  } else {*/
	op = Op.SUBST;
	/* }*/
	if (sort == null) {
	    // schema variable
	    return tf.createSubstitutionTerm
		(op,
		 (SortedSchemaVariable)EnvironmentUtil.getSchemaVariable(env, var),
		 parse2(subst, closure),
		 parse2(term, closure));
	} else {
	    LogicVariable v = new LogicVariable(new Name(var.getText()),
						EnvironmentUtil.getSort(env, sort));
	    Term parsed;
	    parsed = parse2(subst, closure);
	    closure.push(v);
	    parsed =  tf.createSubstitutionTerm(op, v,
						parsed,
						parse2(term, closure));
	    closure.pop(v);
	    return parsed;
	}
    }

    public Object visitFunctionTerm(ParsingStack closure, Identifier id, AstTerm func, AstTerm form,
				    Location location)
    throws ParserException {
	Operator2 function = FunctionOperator.function(TermParserUtil.toName(id));
	try {
	    return TermParserUtil.createTerm(function,
					     parse2(func, closure),
					     parse2(form, closure));
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), id.getLocation());
	}
    }

    public Object visitAbbreviationTerm(ParsingStack closure, Identifier name, Location location)
    throws ParserException {
	return EnvironmentUtil.getAbbreviatedTerm(env, name);
    }
    
    /* --- sequences and sets --- */
    /*
    public Object visitSetTerm (ParsingStack closure, AstTerm[] elems) {
	Term[] elems_t;
	
	if (elems == null) {
	    elems_t = null;
	} else {
	    elems_t = new Term[elems.length];
	    for (int i=0; i<elems.length; i++) {
		elems_t[i] = parse2(elems[i], closure);
	    }
	}
	return TermParserUtil.createSetTerm (elems_t);
	}*/

    public Object visitSequenceTerm(ParsingStack closure, Identifier basesort,
				    AstTerm[] elems, AstTerm tail, Location seqLoc)
	throws ParserException {
	Term[] elems_t;
	Term tail_t = null;
	Sort sort = null;
	
	if (elems == null || elems.length == 0) {
	    if (tail != null) {
		throw new ParserException("There are no head, and tail is not empty",
					  tail.getLocation());
	    } else if (basesort == null) {
		throw new ParserException("The empty list needs an explicit sort", seqLoc);
	    } else {
		elems_t=null;
	    }
	} else {
	    elems_t = new Term[elems.length];
	    for(int i=0; i<elems.length; i++) {
		elems_t[i] = parse2(elems[i], closure); 
	    }
	    
	    if (tail != null) {
		tail_t = parse2(tail, closure);
	    }
	}
	
	if(basesort == null) {
	    sort = elems_t[0].sort();
	} else {
	    sort = EnvironmentUtil.getSort(env, basesort);
	}
	
	Operator2 empty = (Operator2) EnvironmentUtil.
	    getOperator(env, new Identifier(seqLoc, "nil_" + sort.name())); 
	Operator2 cons = (Operator2) EnvironmentUtil.
	    getOperator(env, new Identifier(seqLoc, "cons_" + sort.name()));
	
	try {
	    return TermParserUtil.createSequenceTerm(sort, elems_t, tail_t, empty, cons);
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), seqLoc);
	}
    }

    /* --- dynamic logic terms --- */

    public Object visitBox(ParsingStack closure, AstAsmRule rule, AstTerm term, AstTerm step,
			   Location location) 
    throws ParserException {
	try {
	    return TermParserUtil.createTerm
		((step==null)?AsmOperator.BOX:AsmTimedOperator.TBOX(parse2(step, closure)),
		 parse2(rule, closure),
		 parse2(term, closure)
		 );
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitDiamond(ParsingStack closure, AstAsmRule rule, AstTerm term, AstTerm step,
			       Location location)
    throws ParserException {
	try {
	    return TermParserUtil.createTerm
		((step==null)?AsmOperator.DIAMOND:AsmTimedOperator.TDIAMOND(parse2(step, closure)),
		 parse2(rule, closure),
		 parse2(term, closure)
		 );
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    /* --- ASM rules --- */

    /** Parse an ASM rule with the bound logic variables. The elements
     * of 'logicVariables' have to be of type {@link
     * LogicVariable}. */
    public Term parse(AstAsmRule rule, ListOfOperator logicVariables)
        throws ParserException
    {
	return parse2(rule, new ParsingStack(logicVariables));
    }

    /** Parses an ASM rule recursive. Hint: The method uses a
     * different name, because the signature 'Object' is to general
     * and may be called incidental, if {@link #parse(AstAsmRule,
     * List)} is wanted. */
    private Term parse2(AstAsmRule rule, ParsingStack closure) throws ParserException {
        return (Term) rule.accept(this, closure);
    }

    /* --- Interface: AstAsmRuleVisitor --- */

    public Object visitSeq(ParsingStack closure, AstAsmRule rule1, AstAsmRule rule2,
			   Location location)
    throws ParserException{
	try {
	    return TermParserUtil.createTerm(AsmProgramOperator.SEQ,
					     parse2(rule1, closure),
					     parse2(rule2, closure));
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitPar(ParsingStack closure, AstAsmRule rule1, AstAsmRule rule2,
			   Location location)
    throws ParserException {
	try {
	    return TermParserUtil.createTerm(AsmProgramOperator.PAR,
					     parse2(rule1, closure),
					     parse2(rule2, closure));
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitSkip(ParsingStack closure, Location location)
    throws ParserException {
	try {
	    return TermParserUtil.createTerm(AsmProgramOperator.SKIP);
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitAssign(ParsingStack closure, AstTerm lhs, AstTerm rhs,
			      Location location)
    throws ParserException {
	try {
	    return TermParserUtil.createTerm(AsmProgramOperator.ASSIGN,
					     parse2(lhs, closure),
					     parse2(rhs, closure));
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitCall(ParsingStack closure, Identifier id, AstTerm[] terms, Location location)
    throws ParserException {
	AsmRule p = EnvironmentUtil.getRule(env, id);
	try {
	    if (terms == null) {
		return tf.createFunctionTerm((Function) p, EMPTY_TERMS);
	    } else {
		return tf.createFunctionTerm((Function) p, parse2(terms, closure));
	    }
	} catch (IllegalArgumentException e) {
	    throw new ParserException(e.getMessage(), location);
	} catch (ClassCastException e) {
	    throw new ParserException
		("Operators implementing AsmRule should be dervied from Funciton:" +
		 e.getMessage(), location);
	}
    }

    public Object visitIf(ParsingStack closure, AstTerm formula, AstAsmRule thenRule,
			      AstAsmRule elseRule, Location location)
    throws ParserException {
	try {
	    return TermParserUtil.createTerm(AsmProgramOperator.IF,
					     parse2(formula, closure),
					     parse2(thenRule, closure),
					     parse2(elseRule, closure));
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitCond(ParsingStack closure, AstTerm[] formulas, AstAsmRule[] rules,
			    AstAsmRule otherwiseRule, Location location)
    throws ParserException {
	return null;
    }

    public Object visitLet(ParsingStack closure, Identifier var, Identifier sort,
                           AstTerm term, AstAsmRule rule, Location location)
    throws ParserException {
	try {
	    if (sort == null) {
		return TermParserUtil.createTerm
		    (AsmProgramOperator.LET,
		     (SortedSchemaVariable)EnvironmentUtil.getSchemaVariable(env, var),
		     parse2(term, closure),
		     parse2(rule, closure));
	    } else {
		LogicVariable v = new LogicVariable
		    (new Name(var.getText()),
		     EnvironmentUtil.getSort(env, sort));
		Term parsed;
		parsed = parse2(term, closure);
		closure.push(v);
		parsed =  TermParserUtil.createTerm(AsmProgramOperator.LET, v,
						    parsed, parse2(rule, closure));
		closure.pop(v);
		return parsed;
	    }
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitForall(ParsingStack closure, Identifier var, Identifier sort,
                              AstTerm formula, AstAsmRule rule, Location location)
    throws ParserException {
	try {
	    if (sort == null) {
		return TermParserUtil.createTerm
		    (AsmProgramOperator.FORALL,
		     (SortedSchemaVariable)EnvironmentUtil.getSchemaVariable(env, var),
		     parse2(formula, closure),
		     parse2(rule, closure));
	    } else {
		LogicVariable v = new LogicVariable(new Name(var.getText()),
						    EnvironmentUtil.getSort(env, sort));
		Term parsed;
		closure.push(v);
		parsed = TermParserUtil.createTerm
		    (AsmProgramOperator.FORALL, v,
		     parse2(formula, closure),
		     parse2(rule, closure));
		closure.pop(v);
		return parsed;
	    }
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitTry(ParsingStack closure, AstAsmRule tryRule, AstAsmRule elseRule,
			   Location location)
    throws ParserException {
	try {
	    return TermParserUtil.createTerm(AsmProgramOperator.TRY,
					     parse2(tryRule, closure),
					     parse2(elseRule, closure));
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    public Object visitAsmVariable(ParsingStack closure, Identifier var, Location location)
    throws ParserException {
	if (env.containsOperator(var.name())) {
	    de.uka.ilkd.key.logic.op.Operator op = EnvironmentUtil.getOperator(env, var);
	    if (op instanceof FormalParameter) {
		return ((FormalParameter) op).createTerm(null, EMPTY_TERMS);
	    }
	}
	if (env.containsSchemaVariable(var.name())) {
	    return tf.createVariableTerm(EnvironmentUtil.getSchemaVariable(env, var));
	} else {
	    throw new ParserException("Variable " + var + " not declared.", location);
	}
    }

    public Object visitSubstitution(ParsingStack closure, Identifier var, Identifier sort,
                                    AstTerm subst, AstAsmRule rule, Location location)
    throws ParserException {
	if (sort == null) {
	    // schema variable
	    return tf.createSubstitutionTerm
		(Op.SUBST,
		 (SortedSchemaVariable)EnvironmentUtil.getSchemaVariable(env, var),
		 parse2(subst, closure),
		 parse2(rule, closure));
	} else {
	    LogicVariable v = new LogicVariable(new Name(var.getText()),
						EnvironmentUtil.getSort(env, sort));
	    Term parsed = parse2(subst, closure);
	    closure.push(v);
	    parsed = tf.createSubstitutionTerm(Op.SUBST, v,
					       parsed,
					       parse2(rule, closure));
	    closure.pop(v);
	    return parsed;
	}
    }

    public Object visitMeta(ParsingStack closure, Identifier id, AstAsmRule rule, Location location)
    throws ParserException {
	MetaOperator op = EnvironmentUtil.getMetaOp(env, id);
	try {
	    return TermParserUtil.createTerm((Operator2) op,
					     parse2(rule, closure));
	} catch (TermNotValidException e) {
	    throw new ParserException(e.getMessage(), location);
	}
    }

    /* --- Sequent --- */

    /** Parse a sequent in the current environment. */
    public Sequent parse(AstSequent sequent)
    throws ParserException {
        ParsingStack stack = new ParsingStack();
        return Sequent.createSequent(semiSequent(parse2(toTerms(sequent.getAntList()), stack)),
                                     semiSequent(parse2(toTerms(sequent.getSucList()), stack)));
    }

    private AstTerm[] toTerms(List list) {
        return (AstTerm[]) list.toArray(new AstTerm[list.size()]);
    }

    private Semisequent semiSequent(Term[] terms) {
        Semisequent ss = Semisequent.EMPTY_SEMISEQUENT;
        for (int i = terms.length - 1; i >= 0; --i) {
            ss = ss.insertFirst(new ConstrainedFormula
		(terms[i], Constraint.BOTTOM)).semisequent();
        }
        return ss;
    }

    /* --- static part --- */
    
    /** Parse the given abstract term in the environment 'env' and
r     * return the concrete term. */
    public static Term parseTerm(TermEnvironment env, AstTerm term)
	throws ParserException {
        return parseTerm(env, term, null);
    }

    /** Parse term in the given environment and the bounds logic
     * variables. The elements of 'logicVariables' have to be of type
     * {@link de.uka.ilkd.key.logic.op.LogicVariable}. */
    public static Term parseTerm(TermEnvironment env, AstTerm term, ListOfOperator logicVariables)
	throws ParserException {
        TermParser parser = new TermParser(env);
        return parser.parse(term, logicVariables);
    }

    /** Parse the asm rule in the given environment. */
    public static Term parseAsmRule(TermEnvironment env, AstAsmRule rule)
	throws ParserException {
        return parseAsmRule(env, rule, null);
    }

    /** Parse ASM rule in the context of a list of logic
     * variables. The elements of 'logicVariables' have to be of type
     * {@link de.uka.ilkd.key.logic.op.LogicVariable}. */
    public static Term parseAsmRule(TermEnvironment env, AstAsmRule rule,
				    ListOfOperator logicVariables)
	throws ParserException {
        TermParser parser = new TermParser(env);
        return parser.parse(rule, logicVariables);
    }

    /** Parse a sequent in the given environment. */
    public static Sequent parseSequent(TermEnvironment env, AstSequent sequent)
	throws ParserException {
        TermParser parser = new TermParser(env);
        return parser.parse(sequent);
    }
}
