/** 
 * Created on: Mar 17, 2011
 */
package de.uka.ilkd.key.smt.lang;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

/**
 * 
 * 
 * @author Aboubakr Achraf El Ghazi
 * 
 */

// The name of this class become misleading. Now, I am only distinguishing between unary operators, binary operators and multi operators.
// A more suitable name for this class will be TermMultOp
public class SMTTermMultOp extends SMTTerm {

    private static HashMap<Op, String> bvSymbols;
    private static HashMap<Op,String> intSymbols;
    public enum OpProperty{
	NONE,
	LEFTASSOC,
	RIGHTASSOC,
	FULLASSOC,
	CHAINABLE,
	PAIRWISE
    }

    public enum Op {
	// Bool/Int operator
	IFF, IMPLIES, EQUALS, MUL, DIV, REM,
	LT, LTE, GT, GTE, PLUS, MINUS, AND, OR,XOR, DISTINCT,

	// BitVec operators 
	CONCAT, BVOR, BVAND,  BVNAND, BVNOR, BVXNOR,
	BVSREM, BVSMOD, BVSHL, BVLSHR, BVASHR,
	BVSLT, BVSLE, BVSGT, BVSGE, BVSDIV;

	public SMTTerm getIdem () {
	    switch (this) {
	    case AND:
		return SMTTerm.TRUE;
	    case OR:
		return SMTTerm.FALSE;
	    default:
		throw new RuntimeException("Unexpected: getIdem() is only app. to the Operators 'AND' and 'OR': "+this);
	    }
	}
	public Op sign (boolean pol) {
	    switch (this) {
	    case AND:
		if (pol)
		    return this;
		return OR;
	    case OR:
		if (pol)
		    return this;
		return AND;
	    default:
		throw new RuntimeException("Unexpected: sign(Boolean pol) is only app. to the Operators 'AND' and 'OR': "+this);
	    }
	}
    }

    public static OpProperty getProperty(SMTTermMultOp.Op op){
	switch(op){
	case AND:case OR:  case PLUS: case MUL: return OpProperty.FULLASSOC;
	case MINUS: case XOR: case DIV: return OpProperty.LEFTASSOC;
	case IMPLIES: return OpProperty.RIGHTASSOC;
	case IFF: case EQUALS: /*case LT: case LTE: case GT: case GTE:*/ return OpProperty.CHAINABLE;
	case DISTINCT: return OpProperty.PAIRWISE;
	default: return OpProperty.NONE;
	}
    }

    private static void initMaps(){
	//bitvec
	bvSymbols = new HashMap<Op, String>();
	bvSymbols.put(Op.IFF, "iff");
	bvSymbols.put(Op.IMPLIES, "=>");
	bvSymbols.put(Op.EQUALS, "=");
	bvSymbols.put(Op.AND, "and");
	bvSymbols.put(Op.OR, "or");
	bvSymbols.put(Op.XOR, "xor");
	bvSymbols.put(Op.DISTINCT, "distinct");
	bvSymbols.put(Op.CONCAT, "concat");
	bvSymbols.put(Op.LT, "bvult");
	bvSymbols.put(Op.LTE, "bvule");
	bvSymbols.put(Op.GT, "bvugt");
	bvSymbols.put(Op.GTE, "bvuge");
	bvSymbols.put(Op.MUL, "bvmul");
	bvSymbols.put(Op.DIV, "bvudiv");
	bvSymbols.put(Op.REM, "bvurem");
	bvSymbols.put(Op.PLUS, "bvadd");
	bvSymbols.put(Op.MINUS, "bvsub");
	bvSymbols.put(Op.BVOR, "bvor");
	bvSymbols.put(Op.BVAND, "bvand");
	bvSymbols.put(Op.BVNAND, "bvnand");
	bvSymbols.put(Op.BVNOR, "bvnor");
	bvSymbols.put(Op.BVXNOR, "bvxnor");
	bvSymbols.put(Op.BVSREM, "bvsrem");
	bvSymbols.put(Op.BVSMOD, "bvsmod");
	bvSymbols.put(Op.BVSHL, "bvshl");
	bvSymbols.put(Op.BVLSHR, "bvlshr");
	bvSymbols.put(Op.BVASHR, "bvashr");
	bvSymbols.put(Op.BVSLT, "bvslt");
	bvSymbols.put(Op.BVSLE, "bvsle");
	bvSymbols.put(Op.BVSGT, "bvsgt");
	bvSymbols.put(Op.BVSGE, "bvsge");
	bvSymbols.put(Op.BVSDIV, "bvsdiv");
	//int
	intSymbols = new HashMap<Op, String>();
	intSymbols.put(Op.IFF, "iff");
	intSymbols.put(Op.IMPLIES, "=>");
	intSymbols.put(Op.EQUALS, "=");
	intSymbols.put(Op.LT, "<");
	intSymbols.put(Op.LTE, "<=");
	intSymbols.put(Op.GT, ">");
	intSymbols.put(Op.GTE, ">=");
	intSymbols.put(Op.DISTINCT, "distinct");
	intSymbols.put(Op.MUL, "*");
	intSymbols.put(Op.DIV, "div");
	intSymbols.put(Op.REM, "rem");
	intSymbols.put(Op.PLUS, "+");
	intSymbols.put(Op.MINUS, "-");
    }





    protected List<SMTTerm> subs;
    protected Op operator;

    public SMTTermMultOp(Op operator, List<SMTTerm> subs) {
	this.operator = operator;
	this.subs = subs;
	for (SMTTerm sub : this.subs) {
	    sub.upp = this;
	}
	if(bvSymbols==null || intSymbols==null){
	    initMaps();
	}
    }

    @Override
    public List<SMTTerm> getSubs() {
	return subs;
    }


    public void setSubs(List<SMTTerm> subs) {
	this.subs = subs;
    }


    public Op getOperator() {
	return operator;
    }


    public void setOperator(Op operator) {
	this.operator = operator;
    }

    /** {@inheritDoc} */
    @Override
    public List<SMTTermVariable> getQuantVars() {
	List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
	for(int i = 0; i< subs.size(); i++){
	    vars.addAll(subs.get(i).getQuantVars());
	}
	return vars;
    }

    /** {@inheritDoc} */
    @Override
    public List<SMTTermVariable> getUQVars() {
	List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
	for(int i = 0; i< subs.size(); i++){
	    vars.addAll(subs.get(i).getUQVars());
	}
	return vars;
    }

    /** {@inheritDoc} */
    @Override
    public List<SMTTermVariable> getEQVars() {
	List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
	for(int i = 0; i< subs.size(); i++){
	    vars.addAll(subs.get(i).getEQVars());
	}
	return vars;
    }

    /** {@inheritDoc} */
    @Override
    public List<SMTTermVariable> getVars() {
	List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();

	for(int i = 0; i< subs.size(); i++){
	    vars.addAll(subs.get(i).getVars());
	}
	return vars;
    }


    /** {@inheritDoc} */
    @Override
    public SMTSort sort () {

	switch (operator) {
	case PLUS:
	case MINUS:
	case MUL:
	case DIV:
	case REM:
	case BVASHR:
	case BVSHL:
	case BVSMOD:
	case BVSREM:
	case BVSDIV:
	    //Sanity check
	    if(subs.size()>1){				
		if(!subs.get(0).sort().equals(subs.get(1).sort())){					
		    String error = "Unexpected: binary operation with two diff. arg sorts";
		    error+="\n";
		    error+=this.toSting()+"\n";
		    error+="First sort: "+subs.get(0).sort()+"\n";
		    error+="Second sort: "+subs.get(1).sort()+"\n";
		    throw new RuntimeException(error);					
		}				
	    }
	    return subs.get(0).sort();
	default:
	    return SMTSort.BOOL;
	}
    }

    /** {@inheritDoc} */
    @Override
    public boolean occurs (SMTTermVariable a) {
	for(int i = 0; i < subs.size(); i++){
	    if(subs.get(i).occurs(a))
		return true;
	}
	return false;
    }

    /** {@inheritDoc} */
    @Override
    public boolean occurs (String id) {	
	for(int i = 0; i < subs.size(); i++){
	    if(subs.get(i).occurs(id))
		return true;
	}
	return false;
    }

    /** {@inheritDoc} */
    @Override
    public SMTTerm substitute (SMTTermVariable a, SMTTerm b) {		
	//		LinkedList<Term> newSubs = new LinkedList<Term>();		
	//		for(Term sub : subs){
	//			newSubs.add(sub.substitute(a, b));
	//		}
	//		return new TermMultOp(operator, newSubs);

	if (subs.isEmpty())
	    return this;

	SMTTerm newTerm = subs.get(0).substitute(a, b);
	for (int i = 1; i < subs.size(); i++) {
	    newTerm = newTerm.multOp(operator, subs.get(i).substitute(a, b));
	}
	return newTerm;

    }

    /** {@inheritDoc} */
    @Override
    public SMTTerm substitute (SMTTerm a, SMTTerm b) {

	if (subs.isEmpty())
	    return this;

	if (this.equals(a))
	    return b;

	//		LinkedList<Term> newSubs = new LinkedList<Term>();
	//		for(Term sub : subs){
	//			newSubs.add(sub.substitute(a, b));
	//		}
	//		return new TermMultOp(operator, newSubs);

	SMTTerm newTerm = subs.get(0).substitute(a, b);
	for (int i = 1; i < subs.size(); i++) {
	    newTerm = newTerm.multOp(operator, subs.get(i).substitute(a, b));
	}
	return newTerm;

    }

    /** {@inheritDoc} */
    @Override
    public SMTTerm replace (SMTTermCall a, SMTTerm b) {
	//		LinkedList<Term> newSubs = new LinkedList<Term>();
	//		for(Term sub : subs){
	//			newSubs.add(sub.replace(a, b));
	//		}
	//		return new TermMultOp(operator, newSubs);
	//		
	if (subs.isEmpty())
	    return this;

	SMTTerm newTerm = subs.get(0).replace(a, b);
	for (int i = 1; i < subs.size(); i++) {
	    newTerm = newTerm.multOp(operator, subs.get(i).replace(a, b));
	}
	return newTerm;
    }

    /** {@inheritDoc} */
    @Override
    public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {
	//		LinkedList<Term> newSubs = new LinkedList<Term>();
	//		for(Term sub : subs){
	//			newSubs.add(sub.instantiate(a, b));
	//		}
	//		return new TermMultOp(operator, newSubs);

	if (subs.isEmpty())
	    return this;

	SMTTerm newTerm = subs.get(0).instantiate(a, b);
	for (int i = 1; i < subs.size(); i++) {
	    newTerm = newTerm.multOp(operator, subs.get(i).instantiate(a, b));
	}
	return newTerm;
    }

    @Override
    public SMTTermMultOp copy () {

	List<SMTTerm> newSubs = new LinkedList<SMTTerm>();
	for(SMTTerm t : subs){
	    newSubs.add(t.copy());
	}


	return new SMTTermMultOp(this.operator, newSubs);
    }

    @Override
    public boolean equals (Object term) {

	if (term == null)
	    return false;

	if (this == term)
	    return true;

	if (!(term instanceof SMTTermMultOp)) 
	    return false;
	SMTTermMultOp lt = (SMTTermMultOp) term;

	if (!this.operator.equals(lt.operator))
	    return false;

	if (this.subs.size() != lt.subs.size())
	    return false;

	for (int i = 0; i < this.subs.size(); i++) {
	    if (!this.subs.get(i).equals(lt.subs.get(i)))
		return false;
	}

	return true;
    }

    //	public boolean equals (Term term) {
    //		
    //		if (term == null)
    //			return false;
    //		
    //		if (this == term)
    //			return true;
    //		
    //		if (!(term instanceof TermLogicalOp)) 
    //			return false;
    //		TermLogicalOp lt = (TermLogicalOp) term;
    //		
    //		if (!this.operator.equals(lt.operator))
    //			return false;
    //		
    //		if (this.subs.size() != lt.subs.size())
    //			return false;
    //		
    //		for (int i = 0; i < this.subs.size(); i++) {
    //			if (!this.subs.get(i).equals(lt.subs.get(i)))
    //				return false;
    //		}
    //		
    //		return true;
    //	}
    //
    //	public boolean equals (TermLogicalOp lt) {
    //		if (lt == null)
    //			return false;
    //		
    //		if (this == lt)
    //			return true;
    //		
    //		if (!this.operator.equals(lt.operator))
    //			return false;
    //		
    //		if (this.subs.size() != lt.subs.size())
    //			return false;
    //		
    //		for (int i = 0; i < this.subs.size(); i++) {
    //			if (!this.subs.get(i).equals(lt.subs.get(i)))
    //				return false;
    //		}
    //		
    //		return true;
    //	}

    @Override
    public int hashCode() {
	int ret = operator.hashCode();
	int base = 10;
	int i = 1;

	for (SMTTerm sub : subs) {
	    ret = ret + sub.hashCode() * (base^i);
	    i++;
	}

	return ret;
    }

    private String getSymbol(Op operator, SMTTerm first) {
	boolean isInt = first.sort().equals(SMTSort.INT)&&first.sort().getBitSize()==-1 ;
	String symbol = null;
	if(isInt){
	    symbol = intSymbols.get(operator);
	}
	else{
	    symbol = bvSymbols.get(operator);
	}
	if(symbol==null){
	    throw new RuntimeException("Unknown operator: "+operator);
	}
	return symbol;
    }

    public String toSting (){
	return toString(0);
    }

    public String toString(int nestPos) {

	StringBuffer tab =  new StringBuffer();
	for(int i = 0; i< nestPos; i++) {
	    tab = tab.append(" ");
	}

	StringBuffer buff = new StringBuffer();
	buff.append(tab);

	if (subs.size() == 0)
	    throw new RuntimeException("Unexpected: Empty args for TermLogicalOp ");


	if (subs.size() == 1 && !this.operator.equals(Op.MINUS))
	    return subs.get(0).toString(nestPos);

	String symbol = getSymbol(operator, subs.get(0));
	buff.append("("+symbol);
	for(SMTTerm f : subs){
	    buff.append("\n");
	    buff.append(f.toString(nestPos+1));
	}
	buff.append("\n" + tab + ")");
	return buff.toString();




    }

    public SMTTerm mkChain () {
	SMTTerm ret = SMTTerm.TRUE;
	for (int i = 0; i < subs.size() -1; i++) {
	    SMTTerm subi = subs.get(i);
	    SMTTerm subiPlus1 = subs.get(i+1);
	    ret = ret.and(subi.multOp(operator, subiPlus1));
	}
	return ret;
    }

    //	public LogicalOperator getLogicalOp() {
    //		return logicalOp;
    //	}
    //
    //	public void setLogicalOp(LogicalOperator logicalOp) {
    //		this.logicalOp = logicalOp;
    //	}
    //
    //	public FormulaFunction getArgs() {
    //		return args;
    //	}
    //
    //	public void setArgs(FormulaFunction args) {
    //		this.args = args;
    //	}



}
