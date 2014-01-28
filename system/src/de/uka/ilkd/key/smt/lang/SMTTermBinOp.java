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
public class SMTTermBinOp extends SMTTerm {
	private static HashMap<Op,String> bvSymbols;
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
		// Bool/Int/BitVec operator
		IFF, IMPLIES, EQUALS, MUL, DIV, REM,
		LT, LTE, GT, GTE, PLUS, MINUS, AND, OR,XOR, DISTINCT,

		// BitVec operators 
		CONCAT, BVOR, BVAND,  BVNAND, BVNOR, BVXNOR,
		BVSREM, BVSMOD, BVSHL, BVLSHR, BVASHR,
		BVSLT, BVSLE, BVSGT, BVSGE
	}
	private Op operator;
	private SMTTerm left, right;

	public SMTTermBinOp(Op operator, SMTTerm left, SMTTerm right) {
		
		this.operator = operator;
		this.left = left;
		this.right = right;
		this.left.upp = this;
		this.right.upp = this;
		if(bvSymbols==null || intSymbols==null){
			initMaps();
		}
		
		throw new RuntimeException("BinaryOps are no longer supported.");
	}

	public static OpProperty getProperty(SMTTermBinOp.Op op){
		
	
		switch(op){
		case AND:case OR:  case PLUS: case MUL: return OpProperty.FULLASSOC;
		case MINUS: case XOR: case DIV: return OpProperty.LEFTASSOC;
		case IMPLIES: return OpProperty.RIGHTASSOC;
		case EQUALS: /*case LT: case LTE: case GT: case GTE:*/ return OpProperty.CHAINABLE;
		case DISTINCT: return OpProperty.PAIRWISE;
		default: return OpProperty.NONE;
		}

	}

	private static void initMaps(){
		//bitvec
		bvSymbols = new HashMap<SMTTermBinOp.Op, String>();
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

		//int
		intSymbols = new HashMap<SMTTermBinOp.Op, String>();
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



	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getQuantVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		vars.addAll(left.getQuantVars());
		vars.addAll(right.getQuantVars());
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getUQVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		vars.addAll(left.getUQVars());
		vars.addAll(right.getUQVars());
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getEQVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		vars.addAll(left.getEQVars());
		vars.addAll(right.getEQVars());
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		vars.addAll(left.getVars());
		vars.addAll(right.getVars());
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
			if (!left.sort().equals(right.sort())){
				
				String error = "Unexpected: binary operation with two diff. arg sorts";
				error+="\n";
				error+=this.toSting()+"\n";
				error+="Left sort: "+left.sort()+"\n";
				error+="Right sort: "+right.sort()+"\n";
				throw new RuntimeException(error);
				
			}
				

			return left.sort();
		default:
			return SMTSort.BOOL;
		}
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs (SMTTermVariable a) {
		for(int i = 0; i<getQuantVars().size(); i++){
			if(!a.getId().equals(((SMTTermVariable) getQuantVars().get(i)).getId())){
				return true;
			}
		}
		return ((SMTTermBinOp)  getQuantVars()).occurs(a);
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs (String id) {
		return left.occurs(id) || right.occurs(id);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTermVariable a, SMTTerm b) {
		return left.substitute(a, b).binOp(operator, right.substitute(a, b)); //TODO
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTerm a, SMTTerm b) {

		if (this.equals(a))
			return b;

		return left.substitute(a, b).binOp(operator, right.substitute(a, b)); //TODO
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace (SMTTermCall a, SMTTerm b) {
		return left.replace(a, b).binOp(operator, right.replace(a, b));
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {
		//		return new TermBinOp(operator, (Term) left.instantiate(a, b), (Term) right.instantiate(a, b)); //TODO
		return left.instantiate(a, b).binOp(operator, right.instantiate(a, b));
	}

	public Op getOperator() {
		return operator;
	}

	public void setOperator(Op operator) {
		this.operator = operator;
	}

	public SMTTerm getLeft() {
		return left;
	}

	public void setLeft(SMTTerm left) {
		this.left = left;
	}

	public SMTTerm getRight() {
		return right;
	}

	public void setRight(SMTTerm right) {
		this.right = right;
	}

	@Override
	public SMTTermBinOp copy () {
		return new SMTTermBinOp(this.operator, this.left, this.right);
	}

	@Override
	public boolean equals (Object term) {

		if (this == term)
			return true;

		if (!(term instanceof SMTTermBinOp)) 
			return false;
		SMTTermBinOp bt = (SMTTermBinOp) term;

		return this.operator.equals(bt.operator) && 
		this.left.equals(bt.left) && 
		this.right.equals(bt.right);
	}

	public boolean equals (SMTTermBinOp bt) {

		if (this == bt)
			return true;

		return this.operator.equals(bt.operator) && 
		this.left.equals(bt.left) && 
		this.right.equals(bt.right);
	}

	@Override
	public int hashCode() {
		return operator.hashCode() + right.hashCode()*10 + left.hashCode()*100;
	}

	public String toSting (){
		return toString(0);
	}

	private void extractArgsLeft(SMTTermBinOp binop,List<SMTTerm> args){
		args.add(0, binop.getRight());
		if(binop.getLeft() instanceof SMTTermBinOp && ((SMTTermBinOp)binop.getLeft()).getOperator().equals(binop.getOperator())){
			extractArgsLeft((SMTTermBinOp) binop.getLeft(), args);
		}
		else{
			args.add(0, binop.getLeft());
		}
	}
	private void extractArgsRight(SMTTermBinOp binop,List<SMTTerm> args){
		args.add(binop.getLeft());
		if(binop.getRight() instanceof SMTTermBinOp && ((SMTTermBinOp)binop.getRight()).getOperator().equals(binop.getOperator())){
			extractArgsRight((SMTTermBinOp) binop.getRight(), args);
		}
		else{
			args.add(binop.getRight());
		}
	}

	private void extractArgs(SMTTermBinOp binop,List<SMTTerm> args){
	
		if(binop.getLeft() instanceof SMTTermBinOp && ((SMTTermBinOp)binop.getLeft()).getOperator().equals(binop.getOperator())){
			
			extractArgs((SMTTermBinOp) binop.getLeft(), args);
			
		}
		else{
			
			args.add(binop.getLeft());
		}
		
		if(binop.getRight() instanceof SMTTermBinOp && ((SMTTermBinOp)binop.getRight()).getOperator().equals(binop.getOperator())){
			extractArgs((SMTTermBinOp) binop.getRight(), args);
		}
		else{
			
			args.add(binop.getRight());
		}
		//call--;
	}

	public boolean isChainableBinOp(SMTTerm t){
		return t instanceof SMTTermBinOp && getProperty(((SMTTermBinOp)t).getOperator()).equals(OpProperty.CHAINABLE);
	}

	public String toString(int nestPos) {
		System.err.println("Warning: somehow a binop was created."+this.getOperator());
		StringBuffer tab =  new StringBuffer("");
		for(int i = 0; i< nestPos; i++) {
			tab = tab.append(" ");
		}
		String symbol = getSymbol(operator,left);
		
		
		//
		// TODO: Better implementation
		// To disable the presentation (toString) of ~assoziative binOp as multOp 
		// 1) Out comment this line 2) comment the code (between //{ and //})
		//
//		return tab + "("+ symbol +" \n" +left.toString(nestPos+1)+ "\n"+ right.toString(nestPos+1)+ "\n" + tab + ")";
		
		//{
		OpProperty property = getProperty(getOperator());

		if(property.equals(OpProperty.LEFTASSOC)){

			List<SMTTerm> args = new LinkedList<SMTTerm>();
			extractArgsLeft(this, args);
			String argsString = "";
			for(SMTTerm arg: args){
				argsString+=arg.toString(nestPos+1)+"\n";

			}
			return tab + "("+ symbol + "\n"+argsString + tab + ")";
		}
		else if(property.equals(OpProperty.RIGHTASSOC)){
			List<SMTTerm> args = new LinkedList<SMTTerm>();
			extractArgsRight(this, args);

			String argsString = "";
			for(SMTTerm arg: args){
				argsString+=arg.toString(nestPos+1)+"\n";

			}
			return tab + "("+ symbol + "\n"+argsString + tab + ")";
		}
		else if(property.equals(OpProperty.FULLASSOC)){
			List<SMTTerm> args = new LinkedList<SMTTerm>();
			extractArgs(this, args);
			String chainString = "";
			//if we have an and operation, then we have to check for chainable ops among the arguments
			
			if(this.operator.equals(Op.AND)){
				List<String> chainStrings = checkChainable(nestPos, args);
				if(chainStrings.size()==1 && args.size()==0){					
					return tab + chainStrings.get(0);
				}
				for(String s : chainStrings){
					chainString+= " "+tab+s+"\n";
				}
			}
						
			String argsString = "";
			for(SMTTerm arg: args){
				argsString+=arg.toString(nestPos+1)+"\n";
			}
			return tab + "("+ symbol + "\n"+argsString+chainString + tab + ")";
		}
		else{
			return tab + "("+ symbol +" \n" +left.toString(nestPos+1)+ "\n"+ right.toString(nestPos+1)+ "\n" + tab + ")";
		}
		//}

	}
	
	private List<List<SMTTerm>> searchChains(List<SMTTerm> args,List<Op> ops){
		List<SMTTerm> chainables = new LinkedList<SMTTerm>();
		List<List<SMTTerm>> result = new LinkedList<List<SMTTerm>>();
		for(SMTTerm arg : args){
			if(isChainableBinOp(arg) && !chainables.contains(arg)){
				int start = args.indexOf(arg);
				result.add(extractChain(start, args,ops,chainables));
			}
		}
		
		for(SMTTerm arg : chainables){
			args.remove(arg);
		}
		
		return result;
	}
	
	private List<SMTTerm> extractChain(int start,List<SMTTerm> args,List<Op> ops, List<SMTTerm> chainables){
		List<SMTTerm> chain = new LinkedList<SMTTerm>();
		SMTTermBinOp first = (SMTTermBinOp) args.get(start);
		chainables.add(first);
		Op op = first.getOperator();
		ops.add(op);
		chain.add(first.getLeft());
		chain.add(first.getRight());
		int i = start+1;
		for(;i<args.size();++i){
			SMTTerm arg = args.get(i);
			if(arg instanceof SMTTermBinOp && ((SMTTermBinOp) arg).getOperator().equals(op)){
				SMTTermBinOp binarg = (SMTTermBinOp) arg;
				if(binarg.getLeft().equals(chain.get(chain.size()-1))){
					chain.add(binarg.getRight());
					chainables.add(arg);
				}
				
			}
			else break;
		}
		
		return chain;
	}

	/**
	 * @param nestPos
	 * @param args
	 * @return
	 */
	private List<String> checkChainable(int nestPos, List<SMTTerm> args) {
		List<Op> ops = new LinkedList<SMTTermBinOp.Op>();
		List<List<SMTTerm>> chains = searchChains(args, ops);
		List<String> chainStrings = new LinkedList<String>();
		for(int i=0;i<chains.size();++i){
			List<SMTTerm> chain = chains.get(i);
			Op op = ops.get(i);
			String chainString = "("+getSymbol(op,chain.get(0));
			for(SMTTerm t : chain){
				chainString+= " "+t.toString(nestPos);
			}
			chainString+= ")";
			chainStrings.add(chainString);
		}
		return chainStrings;
	}

	/**
	 * @return
	 */
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


}
