// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;


/** This class is used to perform program transformations needed 
 * for the symbolic execution of a switch-case statement.
 */
public class SwitchToIf extends ProgramMetaConstruct {

    public static int labelCount = 0;
    private boolean noNewBreak = true;


     /** creates a switch-to-if ProgramMetaConstruct 
     * @param _switch the Statement contained by the meta construct 
     */
    public SwitchToIf(SchemaVariable _switch) {
	super("switch-to-if", (ProgramSV)_switch); 
    }


    /** performs the program transformation needed for symbolic
     * program transformation 
     * @return the transformated program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations insts) {
	Switch sw = (Switch) pe;
	int i = 0;
	ExtList extL=new ExtList();
	StatementBlock result;
	Expression defCond=null;
	Label l = new ProgramElementName("_l"+(labelCount++));
	Break newBreak = new Break(l);

	VariableNamer varNamer = services.getVariableNamer();
	ProgramElementName name = varNamer.getTemporaryNameProposal("_var");

	Statement[] ifs = new Statement[sw.getBranchCount()];
	final ExecutionContext ec = insts.getExecutionContext();
	ProgramVariable exV = new LocationVariable
		    (name,
		     sw.getExpression().getKeYJavaType(services, ec));
	VariableSpecification exVSpec 
	    = new VariableSpecification(exV, 
					sw.getExpression().
					getKeYJavaType(services, ec));
	Statement s = new LocalVariableDeclaration
	    (new TypeRef(sw.getExpression().
			 getKeYJavaType(services, ec)),
	     exVSpec);
	result = new StatementBlock(new ImmutableArray<Statement>(s));
	result = 
	    insertStatementInBlock(result,
				   new Statement[]{new CopyAssignment(exV,
								      sw.getExpression())});

        // mulbrich: Added additional null check for enum constants
        if(!(sw.getExpression().getKeYJavaType(services, ec).getJavaType() instanceof PrimitiveType))
            result = 
                insertStatementInBlock(result, mkIfNullCheck(services, exV));

	extL.add(exV);
	sw = changeBreaks(sw, newBreak);
	while(i<sw.getBranchCount()){
	    if(sw.getBranchAt(i) instanceof Case){
		extL.add(((Case) sw.getBranchAt(i)).getExpression());
		ifs[i]=new If(new Equals(extL),
			      new Then(collectStatements(sw, i)));
		extL.remove(((Case)sw.getBranchAt(i)).getExpression());
	    } else{
		for(int j=0;j<sw.getBranchCount();j++){
		    if(sw.getBranchAt(j) instanceof Case){
			extL.add(((Case) sw.getBranchAt(j)).getExpression());
			if(defCond != null){
			    defCond = new LogicalAnd(defCond,new NotEquals(extL));
			}else{
			    defCond = new NotEquals(extL);
			}
			extL.remove(((Case)sw.getBranchAt(j)).getExpression());
		    }
		}
		ifs[i] = new If(defCond,new Then(collectStatements(sw, i)));
	    }
	    i++;
	}
	result = insertStatementInBlock(result, ifs);
	if(noNewBreak){
	    return result;
	}else{
	    return new LabeledStatement(l, result);
	}
    }

    /**
     * return a check of the kind
     * <code>if(v == null) throw new NullPointerException();</code>
     * @return an if-statement that performs a null check, wrapped in a single-element array.
     */
    
    private Statement[] mkIfNullCheck(Services services, ProgramVariable var) {
        Throw t =
                new Throw(new New(new Expression[0], 
                        new TypeRef(
                        services.getJavaInfo().getKeYJavaType(
                                "java.lang.NullPointerException")), null));
        
        final Expression cnd = new Equals(var, NullLiteral.NULL);
        
        return new Statement[] { new If(cnd, new Then(t)) };
    }


    /** inserts the given statements at the end of the block 
     * @param b the Statementblock where to insert
     * @param stmnt array of Statement those have to be inserted
     */
    private StatementBlock insertStatementInBlock(StatementBlock b,
						  Statement[] stmnt) {
	
	Statement[] block = new Statement[b.getStatementCount()+
					  stmnt.length];
	for (int j = 0; j < b.getStatementCount(); j++) {
	    block[j] = b.getStatementAt(j);
	}
	for (int i = 0; i < stmnt.length; i++) {
	    block[i+b.getStatementCount()] = stmnt[i];
	}
	return new StatementBlock(new ImmutableArray<Statement>(block));	
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
	return new Switch(sw.getExpression(), branches);
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
	    if(p instanceof Case) return new Case(((Case)p).getExpression(),s);
	    if(p instanceof Default) return new Default(s);
	    if(p instanceof Catch) return new Catch(((Catch)p).getParameterDeclaration(),
						    new StatementBlock(new ImmutableArray<Statement>(s)));
	    if(p instanceof Finally) return new Finally(new StatementBlock(new ImmutableArray<Statement>(s)));
	    if(p instanceof Then) return new Then(new StatementBlock(new ImmutableArray<Statement>(s)));
	    if(p instanceof Else) return new Else(new StatementBlock(new ImmutableArray<Statement>(s)));
	}
	if(p instanceof If){
	    return new If(((If)p).getExpression(),(Then)recChangeBreaks(((If)p).getThen(),b),
			  (Else) recChangeBreaks(((If)p).getElse(),b));
	}
	if(p instanceof StatementBlock){
	    Statement[] s= new Statement[((StatementBlock)p).getStatementCount()];
	    for(int i=0; i<((StatementBlock)p).getStatementCount(); i++){
		s[i]=(Statement)recChangeBreaks(((StatementBlock)p).getStatementAt(i), b);
	    }
	    return new StatementBlock(new ImmutableArray<Statement>(s));
	}
	if(p instanceof Try){
	    int n=((Try) p).getBranchCount();
	    Branch[] branches = new Branch[n];
	    for(int i=0; i<n; i++){
		branches[i] = (Branch)recChangeBreaks(((Try) p).getBranchAt(i), b);
	    }
	    return new Try((StatementBlock)recChangeBreaks(((Try) p).getBody(), b),branches);
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
	return new StatementBlock(new ImmutableArray<Statement>(stats));
    }



}
