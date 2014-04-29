// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/** 
 * Created on: Mar 17, 2011
 */
package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.smt.lang.SMTTermMultOp.Op;
import de.uka.ilkd.key.smt.lang.SMTTermQuant.Quant;

/**
 * 
 * 
 * @author Aboubakr Achraf El Ghazi
 * 
 */
public abstract class SMTTerm {
	
	protected String comment;

    public SMTTerm upp;

    public abstract boolean occurs(SMTTermVariable a);

    public abstract boolean occurs(String id);

    public abstract SMTSort sort();

    public abstract SMTTerm substitute(SMTTermVariable a, SMTTerm b);

    public abstract SMTTerm substitute(SMTTerm a, SMTTerm b);

    public abstract SMTTerm replace(SMTTermCall a, SMTTerm b);

    public abstract SMTTerm instantiate(SMTTermVariable a, SMTTerm b);

    public abstract SMTTerm copy();

    public static SMTTerm ite(SMTTerm condition, SMTTerm trueCase,
	    SMTTerm falseCase) {

	if (condition == TRUE) {
	    return trueCase;
	}

	if (condition == FALSE) {
	    return falseCase;
	}

	if (trueCase.equals(falseCase)) {
	    return trueCase;
	}

	return new SMTTermITE(condition, trueCase, falseCase);

    }

    public String getComment() {
		return comment;
	}

	public void setComment(String comment) {
		this.comment = comment;
	}

	public List<SMTTermVariable> getQuantVars() {
	// TODO Auto-generated method stub
	return new LinkedList<SMTTermVariable>();
    }

    public List<SMTTermVariable> getUQVars() {
	// TODO Auto-generated method stub
	return new LinkedList<SMTTermVariable>();
    }

    public List<SMTTermVariable> getEQVars() {
	// TODO Auto-generated method stub
	return new LinkedList<SMTTermVariable>();
    }

    public List<SMTTermVariable> getVars() {
	// TODO Auto-generated method stub
	return new LinkedList<SMTTermVariable>();
    }

    public List<SMTTerm> getSubs() {
	// TODO Auto-generated method stub
	return null;
    }

    @Override
    public String toString() {
	return toString(0);
    }

    public String toString(int nestPos) {
	return toString(nestPos);
    }

    /*
     * Convenience methods for initial creation of terms
     */
    public static final SMTTerm FALSE = new SMTTerm.False();
    public static final SMTTerm TRUE = new SMTTerm.True();

    public static SMTTerm call(SMTFunction func, List<SMTTerm> args) {
	return new SMTTermCall(func, args);
    }

    // public static Term call(Function func, List<Term> args) {
    // return new TermCall(func, args);
    // }

    public static SMTTerm call(SMTFunction func, SMTTerms t) {
	return new SMTTermCall(func, t.getTerms());
    }

    public static SMTTerm call(SMTFunction func, SMTTerm... args) {
	List<SMTTerm> argsList = new LinkedList<SMTTerm>();

	if (args != null) {
	    for (SMTTerm arg : args) {
		if (arg instanceof SMTTerms) {
		    SMTTerms terms = (SMTTerms) arg;
		    argsList.addAll(terms.terms);
		    continue;
		}
		argsList.add(arg);
	    }
	}

	return new SMTTermCall(func, argsList);
    }

    public static SMTTerm call(SMTFunction func, List<? extends SMTTerm> args,
	    SMTTerm... moreArgs) {
	List<SMTTerm> argsList = new LinkedList<SMTTerm>();

	if (args != null) {
	    for (SMTTerm arg : args) {
		argsList.add(arg);
	    }
	}
	if (moreArgs != null) {
	    for (SMTTerm arg : moreArgs) {
		argsList.add(arg);
	    }
	}

	return new SMTTermCall(func, argsList);
    }

    // public static Term call(Function func, List<Term> args, Term... moreArgs)
    // {
    // List<Term> argsList = new LinkedList<Term>();
    //
    // if (args != null) {
    // for (Term arg : args) {
    // argsList.add(arg);
    // }
    // }
    // if (moreArgs != null) {
    // for (Term arg : moreArgs) {
    // argsList.add(arg);
    // }
    // }
    //
    // return new TermCall(func, argsList);
    // }

    public static SMTTerm call(SMTFunction func, SMTTerm[]... args) {
	List<SMTTerm> argsList = new LinkedList<SMTTerm>();

	if (args != null) {
	    for (SMTTerm[] termList : args) {
		if (termList != null) {
		    for (SMTTerm term : termList) {
			argsList.add(term);
		    }
		}
	    }
	}

	return new SMTTermCall(func, argsList);
    }

    public static SMTTerm call(SMTFunction func,
	    List<? extends SMTTerm>... args) {
	List<SMTTerm> argsList = new LinkedList<SMTTerm>();

	if (args != null) {
	    for (List<? extends SMTTerm> termList : args) {
		if (termList != null) {
		    for (SMTTerm term : termList) {
			argsList.add(term);
		    }
		}
	    }
	}

	return new SMTTermCall(func, argsList);
    }

    public static SMTTerm call(SMTFunction func, SMTTerm arg) {
	if(func == null){
	    throw new RuntimeException("null call");
	}
	List<SMTTerm> args = new LinkedList<SMTTerm>();
	args.add(arg);
	return new SMTTermCall(func, args);
    }

    public static SMTTerm call(SMTFunction func) {
	List<SMTTerm> args = new LinkedList<SMTTerm>();
	return new SMTTermCall(func, args);
    }

    public static SMTTerm not(SMTTerm subForm) {
	return new SMTTermUnaryOp(SMTTermUnaryOp.Op.NOT, subForm);
    }

    // public static SMTTerm forall(List<TermVariable> bindVars, SMTTerm
    // subForm, SMTTerm pat) {
    // return new TermQuant(Quant.FORALL, bindVars, subForm,
    // toList(toList(pat)));
    // }

    public static SMTTerm forall(List<SMTTermVariable> bindVars, SMTTerm subForm,
	    List<SMTTerm> pats) {
	return new SMTTermQuant(Quant.FORALL, bindVars, subForm, toList(pats));
    }

//    public static SMTTerm forall(TermVariable bindVar, SMTTerm subForm,
//	    SMTTerm pat) {
//	List<TermVariable> bindVars = new LinkedList<TermVariable>();
//	bindVars.add(bindVar);
//	return new TermQuant(Quant.FORALL, bindVars, subForm,
//		toList(toList(pat)));
//    }

    public static SMTTerm forall(SMTTermVariable bindVar, SMTTerm subForm,
	    List<SMTTerm> pats) {
	List<SMTTermVariable> bindVars = new LinkedList<SMTTermVariable>();
	bindVars.add(bindVar);
	return new SMTTermQuant(Quant.FORALL, bindVars, subForm, toList(pats));
    }

    // public static SMTTerm exists(List<TermVariable> bindVars, SMTTerm
    // subForm, SMTTerm pat) {
    // return new TermQuant(Quant.EXISTS, bindVars, subForm,
    // toList(toList(pat)));
    // }

    public static SMTTerm exists(List<SMTTermVariable> bindVars, SMTTerm subForm,
	    List<SMTTerm> pats) {
	return new SMTTermQuant(Quant.EXISTS, bindVars, subForm, toList(pats));
    }

    public static SMTTerm exists(SMTTermVariable bindVar, SMTTerm subForm,
	    SMTTerm pat) {
	List<SMTTermVariable> bindVars = new LinkedList<SMTTermVariable>();
	bindVars.add(bindVar);
	return new SMTTermQuant(Quant.EXISTS, bindVars, subForm,
		toList(toList(pat)));
    }

    public static SMTTerm exists(SMTTermVariable bindVar, SMTTerm subForm,
	    List<SMTTerm> pats) {
	List<SMTTermVariable> bindVars = new LinkedList<SMTTermVariable>();
	bindVars.add(bindVar);
	return new SMTTermQuant(Quant.EXISTS, bindVars, subForm, toList(pats));
    }

    public static SMTTerm number(int n) {
	return new SMTTermNumber(n);
    }

    public static SMTTerm number(int n, int bitSize) {
	if (bitSize < 0)
	    return new SMTTermNumber(n);
	return new SMTTermNumber(n, bitSize,null);
    }

    public SMTTerms terms() {
	if (this instanceof SMTTerms)
	    return (SMTTerms) this;

	List<SMTTerm> termList = new LinkedList<SMTTerm>();
	termList.add(this);
	return new SMTTerms(termList);
    }

    public static SMTTerms terms(List<SMTTerm> terms) {
	return new SMTTerms(terms);
    }

    /*
     * Help object methods for building Terms. An other purpose of the methods,
     * is to perform some (logical) simplification during the Term
     * generation/translation. Some very basic simplification, for sub Terms
     * equal to {TRUE, FALSE}, are already implemented.
     * 
     * TODO more simplification during the translation.
     * ------------------------------------------------
     */

    public SMTTerm unaryOp(SMTTermUnaryOp.Op op) {
	switch (op) {
	case NOT:
	    return this.not();
	default:
	    throw new RuntimeException("Unexpected: unaryOp: " + op);
	}
    }

    public SMTTerm sign(boolean pol) {
	if (pol)
	    return this;
	else
	    return this.not();
    }

    public SMTTerm not() {
	if (this == FALSE)
	    return TRUE;

	if (this == TRUE)
	    return FALSE;

	if (this instanceof SMTTermUnaryOp) {
	    SMTTermUnaryOp ut = (SMTTermUnaryOp) this;
	    if (ut.getOperator().equals(SMTTermUnaryOp.Op.NOT)) {
		return ut.getSub();
	    }
	}

	return new SMTTermUnaryOp(SMTTermUnaryOp.Op.NOT, this);
    }

    public SMTTerm multOp(SMTTermMultOp.Op op, SMTTerm t) {

	switch (op) {
	case AND:
	    return this.and(t);
	case OR:
	    return this.or(t);
	case IMPLIES:
	    return this.implies(t);
	case IFF:
	    return this.iff(t);
	case EQUALS:
	    return this.equal(t);
	case LT:
	    return this.lt(t);
	case LTE:
	    return this.lte(t);
	case DIV:
	    return this.div(t);
	case GT:
	    return this.gt(t);
	case GTE:
	    return this.gte(t);
	case MINUS:
	    return this.minus(t);
	case MUL:
	    return this.mul(t);
	case PLUS:
	    return this.plus(t);
	case REM:
	    return this.rem(t);

	default:
	    return defaultMultOp(op, t);
	    // TODO implement bitvec cases if necessary
	    // throw new
	    // RuntimeException("Unexpected: binOp as arg for the method binOp(): "+op);
	}

    }

    /**
     * @param op
     * @param f
     * @return
     */
    private SMTTerm defaultMultOp(SMTTermMultOp.Op op, SMTTerm f) {
	List<SMTTerm> args = this.toList();
	args.add(f);
	return new SMTTermMultOp(op, args);
    }

    public static SMTTerm or(List<SMTTerm> args) {
	SMTTerm ret = FALSE;
	for (SMTTerm arg : args) {
	    ret = ret.or(arg);
	}
	return ret;
    }

    public SMTTerm or(SMTTerm right) {
	if (right == TRUE)
	    return TRUE;

	if (right == FALSE)
	    return this;

	List<SMTTerm> subForms = new LinkedList<SMTTerm>();

	if (this instanceof SMTTermMultOp) {
	    SMTTermMultOp t = (SMTTermMultOp) this;
	    if (t.operator == Op.OR) {
		subForms.addAll(t.subs);
	    } else {
		subForms.add(this);
	    }
	} else {
	    subForms.add(this);
	}

	if (right instanceof SMTTermMultOp) {
	    SMTTermMultOp t = (SMTTermMultOp) right;
	    if (t.operator == Op.OR) {
		subForms.addAll(t.subs);
	    } else {
		subForms.add(right);
	    }
	} else {
	    subForms.add(right);
	}

	return new SMTTermMultOp(SMTTermMultOp.Op.OR, subForms);

	// return new TermBinOp(TermBinOp.Op.OR, this, f);
    }

    public static SMTTerm and(List<SMTTerm> args) {
	SMTTerm ret = TRUE;
	for (SMTTerm arg : args) {
	    ret = ret.and(arg);
	}
	return ret;
    }

    public SMTTerm and(SMTTerm right) {
	if (right == FALSE)
	    return FALSE;

	if (right == TRUE)
	    return this;

	List<SMTTerm> subForms = new LinkedList<SMTTerm>();

	if (this instanceof SMTTermMultOp) {
	    SMTTermMultOp t = (SMTTermMultOp) this;
	    if (t.operator == Op.AND) {
		subForms.addAll(t.subs);
	    } else {
		subForms.add(this);
	    }
	} else {
	    subForms.add(this);
	}

	if (right instanceof SMTTermMultOp) {
	    SMTTermMultOp t = (SMTTermMultOp) right;
	    if (t.operator == Op.AND) {
		subForms.addAll(t.subs);
	    } else {
		subForms.add(right);
	    }
	} else {
	    subForms.add(right);
	}

	return new SMTTermMultOp(SMTTermMultOp.Op.AND, subForms);

	// return new TermBinOp(TermBinOp.Op.AND, this, f);
    }

    public SMTTerms c(SMTTerm f) {
	List<SMTTerm> subForms = new LinkedList<SMTTerm>();

	if (this instanceof SMTTerms) {
	    SMTTerms t = (SMTTerms) this;
	    subForms.addAll(t.getTerms());
	} else {
	    subForms.add(this);
	}

	if (f instanceof SMTTerms) {
	    SMTTerms t = (SMTTerms) f;
	    subForms.addAll(t.getTerms());
	} else {
	    subForms.add(f);
	}

	return new SMTTerms(subForms);
    }

    public SMTTerm concat(SMTTerm f) {
	List<SMTTerm> subForms = new LinkedList<SMTTerm>();

	if (this instanceof SMTTermMultOp) {
	    SMTTermMultOp t = (SMTTermMultOp) this;
	    if (t.operator == Op.CONCAT) {
		subForms.addAll(t.subs);
	    } else {
		subForms.add(this);
	    }
	} else {
	    subForms.add(this);
	}

	if (f instanceof SMTTermMultOp) {
	    SMTTermMultOp t = (SMTTermMultOp) f;
	    if (t.operator == Op.CONCAT) {
		subForms.addAll(t.subs);
	    } else {
		subForms.add(f);
	    }
	} else {
	    subForms.add(f);
	}

	return new SMTTermMultOp(SMTTermMultOp.Op.CONCAT, subForms);
    }

    public SMTTerm binOp(SMTTermBinOp.Op op, SMTTerm f) {
	throw new RuntimeException("BinaryOps are no longer supported.");

	// switch (op) {
	// case AND:
	// return this.and(f);
	// case OR:
	// return this.or(f);
	// case IMPLIES:
	// return this.implies(f);
	// case IFF:
	// return this.iff(f);
	// case EQUALS:
	// return this.equal(f);
	// case LT:
	// return this.lt(f);
	// case LTE:
	// return this.lte(f);
	// case DIV:
	// return this.div(f);
	// case GT:
	// return this.gt(f);
	// case GTE:
	// return this.gte(f);
	// case MINUS:
	// return this.minus(f);
	// case MUL:
	// return this.mul(f);
	// case PLUS:
	// return this.plus(f);
	// case REM:
	// return this.rem(f);
	//
	// default:
	// //return new TermBinOp(op, this, f);
	// //TODO implement bitvec cases if necessary
	// //throw new
	// RuntimeException("Unexpected: binOp as arg for the method binOp(): "+op);
	// }
    }

    public SMTTerm iff(SMTTerm right) {
	// return new TermBinOp(TermBinOp.Op.IFF, this, right);
	return defaultMultOp(SMTTermMultOp.Op.IFF, right);
    }

    public static SMTTerm implies(List<SMTTerm> args) {
	if (args.size() == 2)
	    return args.get(0).implies(args.get(1));
	return new SMTTermMultOp(SMTTermMultOp.Op.IMPLIES, args);
    }

    public SMTTerm implies(SMTTerm right) {
	if (right == TRUE)
	    return TRUE;

	if (right == FALSE)
	    return this.not();

	if (this == TRUE)
	    return right;

	if (this == FALSE)
	    return TRUE;

	// return new TermBinOp(TermBinOp.Op.IMPLIES, this, right);
	return defaultMultOp(SMTTermMultOp.Op.IMPLIES, right);
    }

    public static SMTTerm equal(List<SMTTerm> args) {
	if (args.size() == 2)
	    return args.get(0).equal(args.get(1));
	return new SMTTermMultOp(SMTTermMultOp.Op.EQUALS, args);
    }

    // For Term (e.g. Boolean valued terms), the equality "=" and equivalent
    // "iff" are in SMT the same. (I hope)
    public SMTTerm equal(SMTTerm right) {
	if (this == right)
	    return TRUE;

	if (this.sort() == SMTSort.BOOL) {

	    if (this == SMTTerm.TRUE) {
		return right;
	    }

	    if (this == SMTTerm.FALSE) {
		return right.not();
	    }

	    if (right == SMTTerm.TRUE) {
		return this;
	    }

	    if (right == SMTTerm.FALSE) {
		return this.not();
	    }

	}

	// return new TermBinOp(TermBinOp.Op.EQUALS, this, right);
	return defaultMultOp(SMTTermMultOp.Op.EQUALS, right);
    }

    public SMTTerm lt(SMTTerm right) {
	// return new TermBinOp(TermBinOp.Op.LT, this, right);
	return defaultMultOp(SMTTermMultOp.Op.BVSLT, right);
    }

    public SMTTerm lte(SMTTerm right) {
	// return new TermBinOp(TermBinOp.Op.LTE, this, right);
	return defaultMultOp(SMTTermMultOp.Op.BVSLE, right);
    }

    public SMTTerm gt(SMTTerm right) {
	// return new TermBinOp(TermBinOp.Op.GT, this, right);
	return defaultMultOp(SMTTermMultOp.Op.BVSGT, right);
    }

    public SMTTerm gte(SMTTerm right) {
	// return new TermBinOp(TermBinOp.Op.GTE, this, right);
	return defaultMultOp(SMTTermMultOp.Op.BVSGE, right);
    }

    public SMTTerm mul(SMTTerm right) {
	if (this instanceof SMTTermNumber) {
	    SMTTermNumber ln = (SMTTermNumber) this;
	    if (ln.getIntValue() == 0)
		//return SMTTerm.number(0);
	    	return SMTTerm.number(0, (int) this.sort().getBitSize());
	    if (ln.getIntValue() == 1) {
		return right;
	    }
	}
	if (right instanceof SMTTermNumber) {
	    SMTTermNumber rn = (SMTTermNumber) right;
	    if (rn.getIntValue() == 0)
		return SMTTerm.number(0, (int) this.sort().getBitSize());
	    if (rn.getIntValue() == 1) {
		return this;
	    }
	}

	// return new TermBinOp(TermBinOp.Op.MUL, this, right);
	return defaultMultOp(SMTTermMultOp.Op.MUL, right);
    }

    public SMTTerm div(SMTTerm right) {
	if (this instanceof SMTTermNumber) {
	    SMTTermNumber ln = (SMTTermNumber) this;
	    if (ln.getIntValue() == 0)
		return SMTTerm.number(0, (int) this.sort().getBitSize());;
	}
	if (right instanceof SMTTermNumber) {
	    SMTTermNumber rn = (SMTTermNumber) right;
	    if (rn.getIntValue() == 1) {
		return this;
	    }
	}

	// return new TermBinOp(TermBinOp.Op.DIV, this, right);
	return defaultMultOp(SMTTermMultOp.Op.BVSDIV, right);
    }

    public SMTTerm rem(SMTTerm right) {
	// return new TermBinOp(TermBinOp.Op.REM, this, right);
	return defaultMultOp(SMTTermMultOp.Op.BVSREM, right);
    }

    public SMTTerm plus(SMTTerm right) {
	if (this instanceof SMTTermNumber) {
	    SMTTermNumber ln = (SMTTermNumber) this;
	    if (ln.getIntValue() == 0)
		return right;
	}
	if (right instanceof SMTTermNumber) {
	    SMTTermNumber rn = (SMTTermNumber) right;
	    if (rn.getIntValue() == 0)
		return this;
	}
	// return new TermBinOp(TermBinOp.Op.PLUS, this, right);
	return defaultMultOp(SMTTermMultOp.Op.PLUS, right);
    }

    public SMTTerm minus(SMTTerm right) {
	if (right instanceof SMTTermNumber) {
	    SMTTermNumber rn = (SMTTermNumber) right;

	    if (rn.getIntValue() == 0)
		return this;
	}
	// return new TermBinOp(TermBinOp.Op.MINUS, this, right);
	return defaultMultOp(SMTTermMultOp.Op.MINUS, right);
    }

    public SMTTerm quant(SMTTermQuant.Quant quant, List<SMTTermVariable> bindVars) {
	switch (quant) {
	case FORALL:
	    return this.forall(bindVars);
	case EXISTS:
	    return this.exists(bindVars);
	default:
	    return this;
	}
    }

    public SMTTerm quant(SMTTermQuant.Quant quant, List<SMTTermVariable> bindVars,
	    List<List<SMTTerm>> pats) {
	switch (quant) {
	case FORALL:
	    return this.forall(bindVars, pats);
	case EXISTS:
	    return this.exists(bindVars, pats);
	default:
	    return this;
	}
    }

    public SMTTerm forall(List<SMTTermVariable> bindVars) {
	return this.forall(bindVars, null);
    }

    public SMTTerm forall(SMTTerms terms) {
	List<SMTTermVariable> bindVars = new LinkedList<SMTTermVariable>();
	for (SMTTerm t : terms.terms) {
	    if (t instanceof SMTTermVariable) {
		bindVars.add((SMTTermVariable) t);
	    }
	}
	return this.forall(bindVars, null);
    }

    public SMTTerm forall(SMTTerms terms, SMTTerm pat) {
	List<SMTTermVariable> bindVars = new LinkedList<SMTTermVariable>();
	for (SMTTerm t : terms.terms) {
	    if (t instanceof SMTTermVariable) {
		bindVars.add((SMTTermVariable) t);
	    }
	}
	return this.forall(bindVars, toList(toList(pat)));
    }

    public SMTTerm forall(SMTTermVariable var) {
	return this.forall(toList(var), null);
    }

    public SMTTerm forall(SMTTermVariable var, SMTTerm pat) {
	return this.forall(toList(var), toList(toList(pat)));
    }

    public SMTTerm forall(SMTTermVariable var, List<List<SMTTerm>> pats) {
	return this.forall(toList(var), pats);
    }

    public SMTTerm forall(List<SMTTermVariable> bindVars, List<List<SMTTerm>> pats) {
	if (bindVars.isEmpty())
	    return this;

	// Correct possible wrong placement of patterns
	// TODO: A more general simplification, which will get ride of nested
	// quantifiers, is the the prenex normal form
	if (this instanceof SMTTermQuant) {
	    SMTTermQuant subQt = (SMTTermQuant) this;
	    if (subQt.getQuant().equals(SMTTermQuant.Quant.FORALL)) {
		if (pats == null && subQt.pats != null)
		    return subQt.sub.forall(bindVars, subQt.bindVars,
			    subQt.pats);
		if (subQt.pats == null && pats != null)
		    return subQt.sub.forall(bindVars, subQt.bindVars, pats);
		if (subQt.pats == null && pats == null)
		    return subQt.sub.forall(bindVars, subQt.bindVars, pats);
	    }
	}

	return new SMTTermQuant(Quant.FORALL, bindVars, this, pats);
    }

    public SMTTerm forall(List<SMTTermVariable> bindVars1,
	    List<SMTTermVariable> bindVars2, List<List<SMTTerm>> pats) {
	List<SMTTermVariable> bindVars = new LinkedList<SMTTermVariable>();
	bindVars.addAll(bindVars1);
	bindVars.addAll(bindVars2);
	if (bindVars.isEmpty())
	    return this;

	return this.forall(bindVars, pats);
    }

    public SMTTerm forall(List<SMTTermVariable> bindVars1,
	    List<SMTTermVariable> bindVars2, SMTTerm pat) {
	List<SMTTermVariable> bindVars = new LinkedList<SMTTermVariable>();
	bindVars.addAll(bindVars1);
	bindVars.addAll(bindVars2);
	if (bindVars.isEmpty())
	    return this;

	return this.forall(bindVars, toList(toList(pat)));
    }

    public SMTTerm exists(SMTTermVariable var) {
	return this.exists(toList(var), null);
    }

    public SMTTerm exists(SMTTermVariable var, SMTTerm pat) {
	return this.exists(toList(var), toList(toList(pat)));
    }

    public SMTTerm exists(List<SMTTermVariable> bindVars) {
	return this.exists(bindVars, null);
    }

    public SMTTerm exists(List<SMTTermVariable> bindVars, List<List<SMTTerm>> pats) {
	if (bindVars.isEmpty())
	    return this;

	// Correct possible wrong placement of patterns
	// TODO: A more general simplification, which will get ride of nested
	// quantifiers, is the the prenex normal form
	if (this instanceof SMTTermQuant) {
	    SMTTermQuant subQt = (SMTTermQuant) this;
	    if (subQt.getQuant() == Quant.EXISTS) {
		if (pats == null && subQt.pats != null)
		    return subQt.sub.exists(bindVars, subQt.bindVars,
			    subQt.pats);
		if (subQt.pats == null && pats != null)
		    return subQt.sub.exists(bindVars, subQt.bindVars, pats);
		if (subQt.pats == null && pats == null)
		    return subQt.sub.exists(bindVars, subQt.bindVars, pats);
	    }
	}

	return new SMTTermQuant(Quant.EXISTS, bindVars, this, pats);
    }

    public SMTTerm exists(List<SMTTermVariable> bindVars1,
	    List<SMTTermVariable> bindVars2, List<List<SMTTerm>> pats) {
	List<SMTTermVariable> bindVars = new LinkedList<SMTTermVariable>();
	bindVars.addAll(bindVars1);
	bindVars.addAll(bindVars2);
	if (bindVars.isEmpty())
	    return this;

	return this.exists(bindVars, pats);
    }

    public static final class True extends SMTTerm {

	/** {@inheritDoc} */
	@Override
	public SMTSort sort() {
	    return SMTSort.BOOL;
	}

	@Override
	public boolean occurs(SMTTermVariable a) {
	    return false;
	}

	@Override
	public SMTTerm sign(boolean pol) {
	    if (pol)
		return this;
	    else
		return SMTTerm.FALSE;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs(String id) {
	    return false;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTermVariable a, SMTTerm b) {
	    return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTerm a, SMTTerm b) {
	    return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace(SMTTermCall a, SMTTerm b) {
	    return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate(SMTTermVariable a, SMTTerm b) {
	    return this;
	}

	@Override
	public SMTTerm copy() {
	    return this;
	}

	@Override
	public String toString() {
	    return "true";
	}

	@Override
	public String toString(int nestPos) {
	    StringBuffer tab = new StringBuffer();
	    for (int i = 0; i < nestPos; i++) {
		tab = tab.append(" ");
	    }

	    return tab + "true";
	}

	@Override
	public SMTTerm or(SMTTerm right) {
	    return this;
	}

	@Override
	public SMTTerm and(SMTTerm right) {
	    return right;
	}

	@Override
	public SMTTerm implies(SMTTerm right) {
	    return right;
	}

	@Override
	public SMTTerm iff(SMTTerm right) {
	    return right;
	}

	@Override
	public SMTTerm forall(List<SMTTermVariable> bindVars,
		List<List<SMTTerm>> pats) {
	    return this;
	}

    }

    public static final class False extends SMTTerm {

	/** {@inheritDoc} */
	@Override
	public SMTSort sort() {
	    return SMTSort.BOOL;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs(SMTTermVariable a) {
	    return false;
	}

	@Override
	public SMTTerm sign(boolean pol) {
	    if (pol)
		return this;
	    else
		return SMTTerm.TRUE;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs(String id) {
	    return false;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTermVariable a, SMTTerm b) {
	    return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTerm a, SMTTerm b) {
	    return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace(SMTTermCall a, SMTTerm b) {
	    return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate(SMTTermVariable a, SMTTerm b) {
	    return this;
	}

	@Override
	public SMTTerm copy() {
	    return this;
	}

	@Override
	public String toString() {
	    return "false";
	}

	@Override
	public String toString(int nestPos) {
	    StringBuffer tab = new StringBuffer();
	    for (int i = 0; i < nestPos; i++) {
		tab = tab.append(" ");
	    }

	    return tab + "false";
	}

	@Override
	public SMTTerm or(SMTTerm right) {
	    return right;
	}

	@Override
	public SMTTerm and(SMTTerm right) {
	    return this;
	}

	@Override
	public SMTTerm implies(SMTTerm right) {
	    return TRUE;
	}

	@Override
	public SMTTerm iff(SMTTerm right) {
	    return right.not();
	}

	@Override
	public SMTTerm forall(List<SMTTermVariable> bindVars,
		List<List<SMTTerm>> pats) {
	    return this;
	}

    }

    public List<SMTTerm> toList() {
	List<SMTTerm> tToList = new LinkedList<SMTTerm>();
	tToList.add(this);
	return tToList;
    }

    public static <T> List<T> toList(T e) {

	if (e == null)
	    return null;

	List<T> eToList = new LinkedList<T>();
	eToList.add(e);
	return eToList;
    }

    // public boolean isCons () {
    // return this.isCons(false);
    // }

    public boolean isCons() {

	if (this instanceof SMTTermNumber)
	    return true;

	// if (Translator.restConstDef) {
	// if (this instanceof TermCall) {
	// TermCall tc = (TermCall) this;
	//
	// return tc.args.isEmpty();
	// } else {
	// return false;
	// }
	// }

	if (this instanceof SMTTermCall) {
	    SMTTermCall tc = (SMTTermCall) this;

	    for (SMTTerm arg : tc.args) {
		if (!arg.isCons())
		    return false;
	    }
	    return true;

	}

	if (this instanceof SMTTermUnaryOp) {
	    SMTTermUnaryOp ut = (SMTTermUnaryOp) this;
	    return ut.getSub().isCons();
	}

	if (this instanceof SMTTermBinOp) {
	    SMTTermBinOp bt = (SMTTermBinOp) this;
	    return bt.getLeft().isCons() && bt.getRight().isCons();
	}

	if (this instanceof SMTTermMultOp) {
	    SMTTermMultOp lt = (SMTTermMultOp) this;
	    for (SMTTerm term : lt.getSubs()) {
		if (!term.isCons())
		    return false;
	    }

	    return true;
	}

	return false;
    }

    // // @Override
    // public boolean equals(Object t) {
    // return super.equals(t);
    // }
    //
    // // @Override
    // public int hashCode (Term t) {
    // return super.hashCode();
    //
    // }
}