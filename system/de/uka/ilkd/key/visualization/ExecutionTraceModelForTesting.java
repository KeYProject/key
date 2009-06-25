// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualization;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.expression.*;
import de.uka.ilkd.key.java.expression.operator.TypeCast;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SetOfProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Debug;


public class ExecutionTraceModelForTesting extends ExecutionTraceModel {

    public ExecutionTraceModelForTesting(TraceElement start, TraceElement end,
               ContextTraceElement she,Node startN, Node endN){
        super(start, end, she, startN, endN);
    }

    public ExecutionTraceModelForTesting(TraceElement start, TraceElement end,
               ContextTraceElement she, long rating, Node startN, Node endN, 
               Integer type){
        super(start, end, she, rating, startN, endN, type);
    }

    /** Returns all ProgramMethods occuring in this trace.
     * In addition to the overwritten method of the parent class
     * this methods additionally collect also method references. 
     * This includes additionally methods that have not been 
     * replace by their bodies through symolic execution. 
     * This is important for black box testing.
     */
    public SetOfProgramMethod getProgramMethods(Services serv){
        SetOfProgramMethod result = super.getProgramMethods(serv);
        TraceElement current = start;
        while(current != TraceElement.END){//modified. Originally: current != end
      
            JavaASTCollector coll = new JavaASTCollector(current.getProgram(), 
                                                            MethodReference.class);
            coll.start();
            ListOfProgramElement l = coll.getNodes();
            IteratorOfProgramElement it = l.iterator();
            while(it.hasNext()){
                MethodReference mr = (MethodReference) it.next();
                //I'm not sure if this is the correct way to determine the ExecutionContext, but I couldn't find a better way.
                ExecutionContext ec = serv.getJavaInfo().getDefaultExecutionContext();
                KeYJavaType refPrefixType =getStaticPrefixType(mr.getReferencePrefix(), ec, serv);
                ProgramMethod pm = mr.method(serv, refPrefixType, ec);
                if(pm != null && !result.contains(pm)){
                    result = result.add(pm);
                }
            }
            current = current.getNextInProof();
    //      current = current.getNextExecuted();
        }
        return result;
    }

    /**Used by getProgramMethods to compute the class of the receiver object of a method reference.
     * The method reference is passed as the first parameter. This code is copied and pasted
     * from key.rule.metaconstruct.MethodCall and extended.*/
    private KeYJavaType getStaticPrefixType(ReferencePrefix refPrefix,ExecutionContext execContext, Services services) {
        if (refPrefix==null || refPrefix instanceof ThisReference && 
                ((ThisReference) refPrefix).getReferencePrefix()==null){ 
            return execContext.getTypeReference().getKeYJavaType();
        } else if(refPrefix instanceof ThisReference){
            return ((TypeReference) ((ThisReference) refPrefix).getReferencePrefix()).getKeYJavaType();
            //((ProgramVariable) services.getTypeConverter().convertToLogicElement(refPrefix).op()).getKeYJavaType();
        }else if (refPrefix instanceof TypeRef) {
            KeYJavaType t = ((TypeRef)refPrefix).getKeYJavaType();
            if (t == null) { //%%%
            Debug.fail();
            }
            return t;
        } else if (refPrefix instanceof ProgramVariable) {
            return ((ProgramVariable)refPrefix).getKeYJavaType();
        } else if (refPrefix instanceof FieldReference) {
            return ((FieldReference)refPrefix).getProgramVariable()
            .getKeYJavaType();
        } else if (refPrefix instanceof SuperReference) {
            KeYJavaType st = services.getJavaInfo().getSuperclass
                    (execContext.getTypeReference().getKeYJavaType());
            return st;  
        } else if (refPrefix instanceof ParenthesizedExpression) {//chrisg: 12.5.2009
            int c=((ParenthesizedExpression) refPrefix).getChildCount();
            ProgramElement pe = ((ParenthesizedExpression) refPrefix).getChildAt(0);
            if(pe instanceof TypeCast){
        	return ((TypeCast)pe).getKeYJavaType( services,execContext);
            }else if (pe instanceof ReferencePrefix){
            	return getStaticPrefixType((ReferencePrefix)pe, execContext, services);
            }else{
                throw new de.uka.ilkd.key.util.NotSupported
                ("Resolving ReferencePrefix failed for the expression"+refPrefix+" because case distinction is not implemented for the subexpression :\n"+
                 pe+ "\n of Type:"+pe.getClass());
            }
        } else {
            throw new de.uka.ilkd.key.util.NotSupported
            ("Resolving ReferencePrefix failed because case distinction is not implemented for case:\n"+
                    refPrefix.getClass()+
                    "\n The execution context is:"+execContext);
        }               
    }

}
