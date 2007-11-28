// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.Desugarable;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.util.KeYExceptionHandler;

/** 
 * represents a proof obligation input to the prover for a DLMethodContract
 */
public class DLHoareTriplePO implements ProofOblInput {

    private ProofAggregate res;
    private Term term;
    private InitConfig initConfig;
    private String name;
    private Contractable[] contractable;
    private String header; // needed to loaded the proof later
    DLMethodContract ct;

    public DLHoareTriplePO(Term t, Modality mod, String header, 
                           String name, Services services, DLMethodContract ct) {
        this.ct = ct;
        this.term = desugar(t, mod);
        this.name = name;
        this.header = header;
        Statement pe  = (Statement) t.sub(1).javaBlock().program();
        Statement unwrapped = DLMethodContract.unwrapBlocks(pe, false);
        if (unwrapped instanceof MethodBodyStatement) {
            contractable = new Contractable[]{
                    ((MethodBodyStatement)unwrapped).
                    getProgramMethod(services)};
        } else if (unwrapped instanceof Contractable){
            contractable = new Contractable[]{(Contractable)unwrapped};
        } else {
            throw new IllegalStateException("DL Hoare Triple Contract defined "
                                           +"on illegal statement "+unwrapped);
        }            
    }

    private static Term desugar(Term fma, Modality mod) {
        TermFactory tf = TermFactory.DEFAULT;
        StatementBlock sta = (StatementBlock)fma.sub(1).javaBlock().program();
        Statement unwrapped = DLMethodContract.unwrapBlocks(sta,true);
        if (unwrapped instanceof Desugarable) {
            sta = (StatementBlock)((Desugarable)unwrapped).desugar();
        }
        Term result = tf.createJunctorTerm
                (Op.IMP, fma.sub(0),
                 tf.createProgramTerm(mod,
                                      JavaBlock.createJavaBlock(sta),
                                      fma.sub(1).sub(0)));

        return result.equals(fma) ? fma : result;
    }

    /** returns the proof obligation term as result of the proof obligation
     * input. If there is still no input available because nothing has
     * been read yet null is returned.
     */
    public ProofAggregate getPO() {
        return res;
    }

//    public void setSettings(ProofSettings settings) {
//      this.settings = settings;
//    }

    /** starts reading the input and modifies the InitConfig of this
     * object with respect to the given modification
     * strategy.
     */
    public void readProblem(ModStrategy mod) throws ProofInputException {
        initConfig.getServices().getNamespaces().
	    programVariables().add(ct.getProgramVariables());	

        Proof p = new Proof(name(), term, header,
                            initConfig.createTacletIndex(),
                            initConfig.createBuiltInRuleIndex(),
                            initConfig.getServices(),
                            initConfig.mergedProofSettings());
        res = ProofAggregate.createProofAggregate(p, name());

    }

    public void setExceptionHandler(KeYExceptionHandler keh){
    }

    public boolean askUserForEnvironment() {
        return false;
    }

    /** reads the Java model that belongs to this input.
     */
    public String readModel() throws ProofInputException {
        return "";
    }

    /** returns the path to the Java model.
     */
    public String getJavaPath() {
        return "";
    }

    /** set the initial configuration used to read an input. It may become
     * modified during reading depending on the modification strategy used
     * for reading.
     */
    public void setInitConfig(InitConfig i) {
        this.initConfig = i;
    }

    public void readSpecs(){
    }

    public void readActivatedChoices() throws ProofInputException {
        //nothing to do
    }

    public SetOfChoice getActivatedChoices() throws ProofInputException {
        return initConfig.getActivatedChoices();
    }

    /** reads the include section and returns an Includes object.
     */
    public Includes readIncludes() throws ProofInputException {
        return null;
    }

    /** returns the name of the proof obligation input.
     */
    public String name() {
        return name;
    }

    /**
     * returns the object for which this proof obligation proves a contract on.
     * In this case we assume that the first program element of the second
     * subterm of the
     * proof obligation is a method body statement of which the according program
     * method is returned.
     */
    public Contractable[] getObjectOfContract() {
        return contractable;
    }

    /**
     * initialises the contract, that is, it adds the proof created by this PO input
     * to the contract if the given contract is the same as that of the PO. Then true 
     * is returned. Otherwise nothing is done and false is returned.
     */
    public boolean initContract(Contract ct) {
        if (ct==this.ct) {
            ct.addCompoundProof(getPO());
            return true;
        } else {
            return false;
        }
    }

    public void startProtocol() {
        // do nothing
    }

    public Term getTerm() {
      return term;
    }

    public void setPO(ProofAggregate po) {
      res = po;
    }
}
