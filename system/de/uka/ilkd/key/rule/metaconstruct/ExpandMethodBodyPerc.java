package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class ExpandMethodBodyPerc extends ProgramMetaConstruct {

    private final SchemaVariable newLocalScope;
    private final SchemaVariable newConstructedScope;
    
    
    public ExpandMethodBodyPerc(SchemaVariable mb, SchemaVariable newLocalScope,
            SchemaVariable newConstructedScope) {
        super(new Name("expand-method-body-perc"), (ProgramSV)mb);
        this.newConstructedScope = newConstructedScope;
        this.newLocalScope = newLocalScope;
    }

    /** 
     * Replaces the MethodBodyStatement shortcut with the full body,
     * performs prefix adjustments in the body (execution context).
     * @param services the Services with all necessary information 
     * about the java programs
     * @param svInst the instantiations esp. of the inner and outer label 
     * @return the transformed program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
                                            Services services,
                                            SVInstantiations svInst) {

        MethodBodyStatement mbs = (MethodBodyStatement) pe;
        MethodReference mr = mbs.getMethodReference();

        ProgramMethod pm = mbs.getProgramMethod(services);
        //mr.method(services, mbs.getBodySource());

        MethodDeclaration methDecl = pm.getMethodDeclaration();

        StatementBlock result = (StatementBlock) mbs.getBody(services); 
        ReferencePrefix newCalled = mbs.getDesignatedContext();
        if (newCalled instanceof TypeReference) {
            // static method
            newCalled = null;
        }
        TypeReference classContext = new TypeRef(mbs.getBodySource());

// removed this again. see bugs #437,#479 -- vladimir
//      result = prettyNewObjectNames(result, methDecl, classContext);

        // at this point all arguments should be program variables
        ArrayOfExpression argsAsParam = mbs.getArguments();

        final HashMap<IProgramVariable, Expression> map = 
            new HashMap<IProgramVariable, Expression>();        
        for (int i = 0; i < argsAsParam.size(); i++) {
            map.put(methDecl.getParameterDeclarationAt(i).
                    getVariableSpecification().getProgramVariable(), 
                    argsAsParam.getExpression(i));
        }
        ProgVarReplaceVisitor paramRepl = 
            new ProgVarReplaceVisitor(result, map, services); 
        paramRepl.start();      
        result = (StatementBlock) paramRepl.result();
        ReferencePrefix callerScope=null;
        if(mr.callerScope()){
            callerScope = svInst.getExecutionContext().getCallerMemoryArea();
        }else if(mr.constructedScope()){
            callerScope = svInst.getExecutionContext().getConstructedMemoryArea();
        }else if(mr.reentrantScope()){
            KeYJavaType ot = services.getJavaInfo().getJavaLangObject();     
            ProgramVariable ma = services.getJavaInfo().getAttribute(ImplicitFieldAdder.IMPLICIT_REENTRANT_SCOPE, ot);
            callerScope = new FieldReference(ma, svInst.getExecutionContext().getRuntimeInstance());
        }else{
            callerScope = svInst.getExecutionContext().getMemoryArea();
        }
        ReferencePrefix constructedScope = (ReferencePrefix) svInst.getInstantiation(newConstructedScope);
        if(mbs.getProgramMethod(services).getMethodDeclaration().externallyConstructedScope()){
            constructedScope = callerScope;
        }
        return 
            new MethodFrame(mbs.getResultVariable(),
                            new ExecutionContext(classContext, 
                                    pm.getName().equals("<runRunnable>")?
                                            newCalled :
                                                (ReferencePrefix) svInst.getInstantiation(newLocalScope),
                                    newCalled, callerScope, constructedScope),
                            result,
                            pm, PositionInfo.UNDEFINED); 
    }
    
    
}
