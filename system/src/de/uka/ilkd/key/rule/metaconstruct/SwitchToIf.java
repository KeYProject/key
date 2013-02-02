// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;


/** This class is used to perform program transformations needed 
 * for the symbolic execution of a switch-case statement.
 */
public class SwitchToIf extends ProgramTransformer {

    public static int labelCount = 0;
    private boolean noNewBreak = true;


     /** creates a switch-to-if ProgramTransformer 
     * @param _switch the Statement contained by the meta construct 
     */
    public SwitchToIf(SchemaVariable _switch) {
	super("switch-to-if", (ProgramSV)_switch); 
    }


    /** performs the program transformation needed for symbolic
     * program transformation 
     * @return the transformated program
     */
    public ProgramElement transform(ProgramElement pe,
					    Services services,
					    SVInstantiations insts) {
	Switch sw = (Switch) pe;
	int i = 0;
	ExtList extL=new ExtList();
	StatementBlock result;
	Expression defCond=null;
	Label l = new ProgramElementName("_l"+(labelCount++));
	Break newBreak = KeYJavaASTFactory.breakStatement(l);

	VariableNamer varNamer = services.getVariableNamer();
	ProgramElementName name = varNamer.getTemporaryNameProposal("_var");

	Statement[] ifs = new Statement[sw.getBranchCount()];
	final ExecutionContext ec = insts.getExecutionContext();
	ProgramVariable exV = KeYJavaASTFactory.localVariable(name, sw
		.getExpression().getKeYJavaType(services, ec));
	Statement s = KeYJavaASTFactory.declare(name, sw.getExpression()
		.getKeYJavaType(services, ec));
	result = KeYJavaASTFactory.block(s,
		KeYJavaASTFactory.assign(exV, sw.getExpression()));

        // mulbrich: Added additional null check for enum constants
        if(!(sw.getExpression().getKeYJavaType(services, ec).getJavaType() instanceof PrimitiveType))
	    result = KeYJavaASTFactory.insertStatementInBlock(result,
		    mkIfNullCheck(services, exV));

	extL.add(exV);
	sw = changeBreaks(sw, newBreak);
	while(i<sw.getBranchCount()){
	    if(sw.getBranchAt(i) instanceof Case){
		extL.add(((Case) sw.getBranchAt(i)).getExpression());
		ifs[i] = KeYJavaASTFactory.ifThen(
			KeYJavaASTFactory.equalsOperator(extL),
			collectStatements(sw, i));
		extL.remove(((Case)sw.getBranchAt(i)).getExpression());
	    } else{
		for(int j=0;j<sw.getBranchCount();j++){
		    if(sw.getBranchAt(j) instanceof Case){
			extL.add(((Case) sw.getBranchAt(j)).getExpression());
			if(defCond != null){
			    defCond = KeYJavaASTFactory.logicalAndOperator(
				    defCond,
				    KeYJavaASTFactory.notEqualsOperator(extL));
			}else{
			    defCond = KeYJavaASTFactory.notEqualsOperator(extL);
			}
			extL.remove(((Case)sw.getBranchAt(j)).getExpression());
		    }
		}
		ifs[i] = KeYJavaASTFactory.ifThen(defCond,
			collectStatements(sw, i));
	    }
	    i++;
	}
	result = KeYJavaASTFactory.insertStatementInBlock(result, ifs);
	if(noNewBreak){
	    return result;
	}else{
	    return KeYJavaASTFactory.labeledStatement(l, result);
	}
    }

    /**
     * return a check of the kind
     * <code>if(v == null) throw new NullPointerException();</code>
     * @return an if-statement that performs a null check, wrapped in a single-element array.
     */
    
    private Statement[] mkIfNullCheck(Services services, ProgramVariable var) {
	final New exception = KeYJavaASTFactory
		.newOperator(services.getJavaInfo().getKeYJavaType(
			"java.lang.NullPointerException"));
	Throw t = KeYJavaASTFactory.throwClause(exception);
        
	final Expression cnd = KeYJavaASTFactory.equalsNullOperator(var);
        
	return new Statement[] { KeYJavaASTFactory.ifThen(cnd, t) };
    }

    /**
     * Replaces all breaks in <code>sw</code>, whose target is sw, with <code>b</code>
     */
    private Switch changeBreaks(Switch sw, Break b){
	int n = sw.getBranchCount();
	Branch[] branches = new Branch[n];
	for(int i=0; i<n; i++){
	    branches[i] = (Branch)recChangeBreaks(sw.getBranchAt(i), b);
	}
	return KeYJavaASTFactory.switchBlock(sw.getExpression(), branches);
    }

    private ProgramElement recChangeBreaks(ProgramElement p, Break b){
	if(p == null) return null;
	if(p instanceof Break && ((Break)p).getLabel() == null){
	    noNewBreak = false;
	    return b;
	}
	if(p instanceof Branch){
	    Statement[] s= new Statement[((Branch)p).getStatementCount()];
	    for(int i=0; i<((Branch)p).getStatementCount(); i++){
		s[i]=(Statement)recChangeBreaks(((Branch)p).getStatementAt(i), b);
	    }
	    if (p instanceof Case)
		return KeYJavaASTFactory.caseBlock(((Case) p).getExpression(),
			s);
	    if (p instanceof Default)
		return KeYJavaASTFactory.defaultBlock(s);
	    if (p instanceof Catch)
		return KeYJavaASTFactory.catchClause(
			((Catch) p).getParameterDeclaration(), s);
	    if (p instanceof Finally)
		return KeYJavaASTFactory.finallyBlock(s);
	    if (p instanceof Then)
		return KeYJavaASTFactory.thenBlock(s);
	    if (p instanceof Else)
		return KeYJavaASTFactory.elseBlock(s);
	}
	if(p instanceof If){
	    return KeYJavaASTFactory.ifElse(((If) p).getExpression(),
		    (Then) recChangeBreaks(((If) p).getThen(), b),
		    (Else) recChangeBreaks(((If) p).getElse(), b));
	}
	if(p instanceof StatementBlock){
	    Statement[] s= new Statement[((StatementBlock)p).getStatementCount()];
	    for(int i=0; i<((StatementBlock)p).getStatementCount(); i++){
		s[i]=(Statement)recChangeBreaks(((StatementBlock)p).getStatementAt(i), b);
	    }
	    return KeYJavaASTFactory.block(s);
	}
	if(p instanceof Try){
	    int n=((Try) p).getBranchCount();
	    Branch[] branches = new Branch[n];
	    for(int i=0; i<n; i++){
		branches[i] = (Branch)recChangeBreaks(((Try) p).getBranchAt(i), b);
	    }
	    return KeYJavaASTFactory.tryBlock(
		    (StatementBlock) recChangeBreaks(((Try) p).getBody(), b),
		    branches);
	}
	return p;
    }

    /**
     * Collects the Statements in a switch statement from branch <code>count</code>
     * downward.
     * @param s the switch statement.
     * @param count the branch where the collecting of statements starts.
     */
    private StatementBlock collectStatements(Switch s, int count){
	int n=0;
	int k=0;
	Statement[] stats;
	for(int i=count; i<s.getBranchCount(); i++){
	    n+=s.getBranchAt(i).getStatementCount();
	}
	stats = new Statement[n];
	for(int i=count; i<s.getBranchCount(); i++){
	    for(int j=0; j<s.getBranchAt(i).getStatementCount();j++){
		stats[k]=s.getBranchAt(i).getStatementAt(j);
		k++;
	    }
	}
	return KeYJavaASTFactory.block(stats);
    }



}
