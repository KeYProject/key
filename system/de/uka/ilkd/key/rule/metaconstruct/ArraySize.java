package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Iterator;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Creates a function term arraySize(sizeOf(type),d_1,...,d_n) from an expression 
 * new type[d_1,...,d_n].
 */
public class ArraySize extends AbstractMetaOperator {

  
    public ArraySize() {
        super(new Name("#arraySize"), 1);
    }

    /**
     * Creates a function term arraySize_type(d_1,...,d_n) from an expression 
     * new type[d_1,...,d_n].
     */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
//        ProgramVariable v0 = (ProgramVariable) term.sub(0).op();
        Iterator<SchemaVariable> it = svInst.svIterator();
        TermFactory tf = TermFactory.DEFAULT;
        NewArray na=null;
        while(it.hasNext()){
            SchemaVariable sv = it.next();
            if(((SchemaVariableAdapter) sv).sort() == ProgramSVSort.NEWARRAY){
                na = (NewArray) svInst.getInstantiation(sv);          
            }
        }
        if(na.getArrayInitializer()!=null){
            return term.sub(0);
        }
//        System.out.println(na.getArguments().getExpression(0).getClass());
        Term dim=null;

        if(ProgramSVSort.SIMPLEEXPRESSION.canStandFor((ProgramElement) na.getArguments().get(0), 
                svInst.getExecutionContext(), services)){
            dim = services.getTypeConverter().convertToLogicElement(
                    na.getArguments().get(0), svInst.getExecutionContext());
        }else{
            return term.sub(0);
        }
        Namespace funcs = services.getNamespaces().functions();
        
        Term scopeTerm;
        ReferencePrefix callerScope=null;
        if(na.callerScope()){
            callerScope = svInst.getExecutionContext().getCallerMemoryArea();
        }else if(na.constructedScope()){
            callerScope = svInst.getExecutionContext().getConstructedMemoryArea();
        }else if(na.reentrantScope()){
            KeYJavaType ot = services.getJavaInfo().getJavaLangObject();     
            ProgramVariable ma = services.getJavaInfo().getAttribute("memoryArea", ot);
            callerScope = new FieldReference(ma, svInst.getExecutionContext().getRuntimeInstance());
        }else{
            callerScope = svInst.getExecutionContext().getMemoryArea();
        }
        scopeTerm =  services.getTypeConverter().convertToLogicElement(callerScope, svInst.getExecutionContext());
        
        ProgramVariable consumed = services.getJavaInfo().getAttribute("consumed", 
                services.getJavaInfo().getKeYJavaTypeByClassName("javax.realtime.MemoryArea"));
        Term heapSpaceTerm = tf.createAttributeTerm(consumed, scopeTerm);
//        Term heapSpaceTerm = tf.createAttributeTerm(consumed, term.sub(1));
//        ProgramVariable heapSpace = (ProgramVariable) services.getNamespaces().
//            programVariables().lookup(new Name(ProblemInitializer.heapSpaceName));
//        Term heapSpaceTerm = tf.createVariableTerm(heapSpace);
        Function sizeFunc;
        String baseType = ((ArrayType) na.getKeYJavaType().getJavaType()).
            getBaseType().getKeYJavaType().getSort().toString();
        Term entrySize = null;
        sizeFunc = (Function) funcs.lookup(new Name("arraySize"));
        if(na.getDimensions()>1){
            IntLiteral lit = new IntLiteral("4");
            entrySize = services.getTypeConverter().convertToLogicElement(lit);
        }else if(baseType.equals("jbyte") || baseType.equals("boolean")){
            IntLiteral lit = new IntLiteral("1");
            entrySize = services.getTypeConverter().convertToLogicElement(lit);
        }else if(baseType.equals("jshort") || baseType.equals("jchar")){
            IntLiteral lit = new IntLiteral("2");
            entrySize = services.getTypeConverter().convertToLogicElement(lit);
        }else if(baseType.equals("jlong")){
            IntLiteral lit = new IntLiteral("8");
            entrySize = services.getTypeConverter().convertToLogicElement(lit);
        }else{
            IntLiteral lit = new IntLiteral("4");
            entrySize = services.getTypeConverter().convertToLogicElement(lit);
        }
        Term size = tf.createFunctionTerm(sizeFunc, entrySize, dim);
        return tf.createUpdateTerm(heapSpaceTerm,
                tf.createFunctionTerm((TermSymbol) funcs.lookup(new Name("add")),
                        heapSpaceTerm, size), term.sub(0));
    }

}
