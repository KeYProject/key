package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.mgt.InstantiatedMethodContract;
import de.uka.ilkd.key.rule.UseMethodContractRule;
import de.uka.ilkd.key.rule.metaconstruct.ExpandMethodBody;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class UseMethodContractRuleForTestGen extends UseMethodContractRule {
    
    /** The only instance of this rule */
    public static UseMethodContractRule INSTANCE = new UseMethodContractRuleForTestGen();

    private Name name = new Name("Use Method Contract (TestCase Gen. version)");
    
    private UseMethodContractRuleForTestGen() {
    }
    
    protected UseMethodContractRule getContractRule() {
        return UseMethodContractRuleForTestGen.INSTANCE;
    }
    
    /**
     * returns the name of this rule
     */
    public Name name() {
        return name;
    }
        
    protected Term preFma(InstantiatedMethodContract iCt, 
            MbsInfo mbsPos, UpdateFactory uf, 
            Update u, Services services){

        ExpandMethodBody exMB = new ExpandMethodBody(mbsPos.mbs);
        StatementBlock methodReplaceStatements = 
            new StatementBlock((Statement) exMB.symbolicExecution(
                    mbsPos.mbs, services, null));

        final Term focus = mbsPos.pio.subTerm();
        final JavaNonTerminalProgramElement all = 
            (JavaNonTerminalProgramElement)focus.javaBlock().program();     
        final NonTerminalProgramElement npe = 
            replaceStatement(all, mbsPos, methodReplaceStatements);
        Term restFma = TermBuilder.DF.tf().createProgramTerm(iCt.getModality(), 
                JavaBlock.createJavaBlock((StatementBlock)npe), 
                focus.sub(0));        

        return uf.apply(u, restFma);
//      return postFmaHelp(iCt, mbsPos, uf, u, methodReplaceStatements, extraPre);
    }
    
    protected String getPreLabel() {
        return "Expanded Method Body";
    }

}
