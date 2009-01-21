package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfOperationContract;

public abstract class ScopeSpec extends AbstractMetaOperator {

    ScopeSpec(Name name, int arity){
        super(name, arity);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services, boolean localScope) {
        MethodBodyStatement mb = getMethodBodyStatement(term.sub(0));
        ProgramMethod pm = mb.getProgramMethod(services);
        SetOfOperationContract contracts = services.getSpecificationRepository()
                  .getOperationContracts(pm, Op.DIA);
        if(contracts.size() == 0) {
            IntLiteral lit = new IntLiteral("0");
            return services.getTypeConverter().convertToLogicElement(lit);
        }
        OperationContract contract = contracts.iterator().next();
        
        Term actualSelf = (mb.getDesignatedContext() instanceof Expression
           ? services.getTypeConverter()
                     .convertToLogicElement(mb.getDesignatedContext())
           : null);
        ListOfTerm actualParams = SLListOfTerm.EMPTY_LIST;
        ArrayOfExpression args = mb.getArguments();
        for(int i = 0; i < args.size(); i++) {
            actualParams = actualParams.append(
                    services.getTypeConverter()
                            .convertToLogicElement(args.getProgramElement(i)));
        }
        

        Term ws = localScope ? contract.getWorkingSpace(actualSelf, actualParams, services) :
            contract.getConstructedWorkingSpace(actualSelf, actualParams, services);
        if(ws==null){
            IntLiteral lit = new IntLiteral("0");
            ws = services.getTypeConverter().convertToLogicElement(lit);
        }
        return ws;
    }
    
    private MethodBodyStatement getMethodBodyStatement(Term t){
        ProgramElement p = t.javaBlock().program();
        while(!(p instanceof MethodBodyStatement)){
            if(p instanceof StatementBlock){
                p = ((StatementBlock) p).getStatementAt(0);
            }else{
                p = (ProgramElement) p.getFirstElement();
            }
        }
        return (MethodBodyStatement) p;
    }
    
}
