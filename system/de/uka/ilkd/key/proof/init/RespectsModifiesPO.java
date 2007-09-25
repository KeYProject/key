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
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SLTranslationError;
import de.uka.ilkd.key.util.ExtList;


/**
 * The "RespectsModifies" proof obligation. 
 */
public class RespectsModifiesPO extends EnsuresPO {
    
    private final OperationContract contract;
    private Term updateAnonMethodTerm = null;
    
    
    public RespectsModifiesPO(OperationContract contract,
                              InvariantSelectionStrategy invStrategy) {
        super("RespectsModifies", 
              contract.getModelMethod(), 
              Modality.BOX, 
              invStrategy,
              true);
        this.contract = contract;
    }
    
    
    private void buildUpdateAnonMethodTerm(ProgramVariable selfVar, 
                                           ListOfProgramVariable paramVars) throws SLTranslationError {
        if(updateAnonMethodTerm != null) {
            return;
        }
        
        //build method declaration
        ExtList extList = new ExtList();
        ProgramElementName name = new ProgramElementName("anonMethod");
        extList.addLast(name);
        MethodDeclaration methodDecl = new MethodDeclaration(extList, false);
        
        //build program method
        ProgramMethod programMethod = new ProgramMethod(methodDecl, 
                                                        javaInfo.getJavaLangObject(), 
                                                        javaInfo.getJavaLangObject(), 
                                                        PositionInfo.UNDEFINED);
        
        //build java block
        ProgramVariable pseudoSelfVar 
                = new LocationVariable(new ProgramElementName("anonObject"), 
                                      Sort.NULL);
        MethodBodyStatement call 
                = new MethodBodyStatement(programMethod,
                                          pseudoSelfVar,
                                          null,
                                          new ArrayOfExpression());/*paramVars*/
        StatementBlock sb = new StatementBlock(call);
        JavaBlock jb = JavaBlock.createJavaBlock(sb);
        
        //build program term
        Term programTerm = tb.dia(jb, tb.tt());
        
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
                              Map atPreFunctions) throws SLTranslationError {
        buildUpdateAnonMethodTerm(selfVar, paramVars);
        Term preTerm = translatePre(contract, selfVar, toPV(paramVars));
        Term result = tb.and(preTerm, updateAnonMethodTerm);
        return result;
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map atPreFunctions) throws SLTranslationError {
        buildUpdateAnonMethodTerm(selfVar, paramVars);
        createAtPreFunctionsForTerm(updateAnonMethodTerm, atPreFunctions);
        Term result = replaceOps(atPreFunctions, updateAnonMethodTerm);
        return result;
    }
}
