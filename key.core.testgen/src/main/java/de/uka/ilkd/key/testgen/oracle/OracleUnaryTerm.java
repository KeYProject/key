package de.uka.ilkd.key.testgen.oracle;

import java.util.HashMap;
import java.util.Map;

public class OracleUnaryTerm implements OracleTerm{
	
	
	
	public enum Op  {Neg, Minus};
	public static String OP_NEG = "!";
	public static String OP_MINUS = "-";
	private static Map<Op,String> op2String;
	
	static{
		op2String = new HashMap<OracleUnaryTerm.Op, String>();
		op2String.put(Op.Neg, OP_NEG);
		op2String.put(Op.Minus, OP_MINUS);
	}
	
	
	private OracleTerm sub;
	private Op op;

	public OracleUnaryTerm(OracleTerm sub, Op op) {
		this.sub = sub;
		this.op = op;
	}
	
	
	
	public Op getOp() {
		return op;
	}



	public OracleTerm getSub() {
		return sub;
	}
	
	public String toString(){
		return op2String.get(op)+sub.toString();
	}
}
