package de.uka.ilkd.key.visualization;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.proof.Node;

/** This trace element can represent a modality (or program) on which
 * symbolic execution didn't take place yet. This is useful for constructing
 * traces for black-box testing.
 * @author gladisch*/
public class UnexecutedTraceElement extends TraceElement {
    /**Determins whether the traced modality is in the antecdent. This is usually
     * determined from posOfModality, but if no symbolic execution takes
     * place posOfModality may be null.*/
    private Boolean inAntec=null;
    
    /** This trace element can represent a modality (or program) on which
     * symbolic execution didn't take place yet. This is useful for constructing
     * traces for black-box testing.
     * @author gladisch*/
    public UnexecutedTraceElement(SourceElement prElement, ProgramElement program, Boolean inAntec, Node n,  TraceElement nip, ContextTraceElement ne, IExecutionContext exCont){
        node = n;
        try{
            /*if no symbolic execution took place yet, getAppliedRuleApp() may be null. 
             Maybe posOfModality can always be null, but I'm not sure.*/
            posOfModality = n.getAppliedRuleApp().posInOccurrence();
        }catch(NullPointerException npe){
            posOfModality = null;
            //alternative way to determine the position of the modality.
            assert inAntec!=null;
            this.inAntec = inAntec;
        }
        nextInProof = nip;
        stepInto = ne;
        programElement = prElement;
        executionContext = exCont;
        this.program = program;
    }

    public Boolean isInAntec(){
        if(getPosOfModality()!=null){
            return getPosOfModality().isInAntec();
        }else{
            return inAntec;
        }
    }

}
