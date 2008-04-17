// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;
import de.uka.ilkd.key.util.ExtList;


/**
 * The "RespectsModifies" proof obligation. 
 */
public class RespectsModifiesPO extends EnsuresPO {
    
    private final OperationContract contract;
    
    private Term updateAnonMethodTerm = null;
    
    
    public RespectsModifiesPO(InitConfig initConfig,
	    		      OperationContract contract,
                              SetOfClassInvariant assumedInvs) {
        super(initConfig,
              "RespectsModifies", 
              contract.getProgramMethod(), 
              Modality.BOX, 
              assumedInvs,
              true);
        this.contract = contract;
    }
    
    
    private void buildUpdateAnonMethodTerm(ProgramVariable selfVar, 
                                           ListOfProgramVariable paramVars) 
    		throws ProofInputException {
        if(updateAnonMethodTerm != null) {
            return;
        }
               
        //build method declaration
        ExtList extList = new ExtList();
        ProgramElementName methodName = new ProgramElementName("anonMethod");
        extList.add(methodName);
        extList.add(new Static());
        MethodDeclaration methodDecl = new MethodDeclaration(extList, false);
        
        //build program method
        ProgramMethod programMethod = new ProgramMethod(methodDecl, 
                                                        javaInfo.getJavaLangObject(), 
                                                        null, 
                                                        PositionInfo.UNDEFINED);
        
        //build java block
        MethodBodyStatement call 
                = new MethodBodyStatement(programMethod,
                                          javaInfo.createTypeReference(javaInfo.getJavaLangObject()),
                                          null,
                                          new ArrayOfExpression());
        StatementBlock sb = new StatementBlock(call);
        JavaBlock jb = JavaBlock.createJavaBlock(sb);
        
        //build program term
        Term programTerm = TB.dia(jb, TB.tt());
        
        //add update
        updateAnonMethodTerm = translateModifies(contract, 
                                                 programTerm, 
                                                 selfVar,
                                                 toPV(paramVars));
    }
        
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        buildUpdateAnonMethodTerm(selfVar, paramVars);
        Term preTerm = translatePre(contract, selfVar, toPV(paramVars));
        Term result = TB.and(preTerm, updateAnonMethodTerm);
        return result;
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) 
    		throws ProofInputException {
        buildUpdateAnonMethodTerm(selfVar, paramVars);
        APF.createAtPreFunctionsForTerm(updateAnonMethodTerm, 
                                        atPreFunctions, 
                                        services);
        Term result = replaceOps(atPreFunctions, updateAnonMethodTerm);
        return result;
    }
    
    
    
    public boolean equals(Object o) {
        if(!(o instanceof RespectsModifiesPO)) {
            return false;
        }
        RespectsModifiesPO po = (RespectsModifiesPO) o;
        return super.equals(po)
               && contract.equals(po.contract);
    }
    
    
    public int hashCode() {
        return super.hashCode() + contract.hashCode();
    }
}
