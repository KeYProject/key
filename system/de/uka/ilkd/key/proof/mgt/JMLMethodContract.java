// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.proof.mgt;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.jml.JMLLemmaMethodSpec;
import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.proof.init.JMLPostAndInvPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * @deprecated
 */
public class JMLMethodContract extends DefaultOperationContract {

    //iff true all existing invariants are added to the pre- and postcondition
    //of the method contract, iff false only the invariants of the containing
    //type and the instance invariants (if meth is not static) for the
    //corresponding object are added. History constraints of the current type
    //are always added.
    public static final boolean allInvariants = true;
    private ModelMethod meth;
    private Modality modality;

    private JMLMethodSpec spec;

    public JMLMethodContract(ModelMethod meth, JMLMethodSpec spec,
                             Modality modality) {
        this.meth = meth;
        this.spec = spec;
        this.modality = modality;
    }

    public void addCompoundProof(ProofAggregate pl) {
        proofs.add(pl);
    }

    public boolean applicableForModality(Modality mod) {
        return getModality().equals(ModalityClass.getNormReprModality(mod));
    }

    public DLMethodContract createDLMethodContract(Proof proof) {
        return new DLMethodContract(getPre(), getPost(), 
                spec.getPi1Functional(), spec.introducedConstants(),                
                (Statement) spec.getProofStatement(),
                spec.getAssignable(),
                modality,
                "Derived JML Method Contract", 
                "Derived JML Method Contract",
                spec.getServices(), spec.getNamespaces());
    }

    public boolean equals(Object cmp) {
        if (!(cmp instanceof JMLMethodContract)) return false;
        final JMLMethodContract mc = (JMLMethodContract)cmp;
        return meth.equals(getObjectOfContract()) &&
            getModality() == mc.getModality() &&
            getSpec().equals(mc.getSpec());
    }

    protected Term getAdditionalAxioms() {
        return spec.getPi1Functional();
    }

    public CatchAllStatement getCatchAllStatement() {        
        return spec.getCatchAllStatement();
    }

    public String getHTMLText() {
        return "<html>pre: "+getPreText()+"<br>post: "
        +getPostText()+"<br>modifies: "
        +getModifiesText()+"<br>termination: "
        +(getModality()==Op.DIA ? "total" : getModality().toString())
        +"</html>";
    }

    public Modality getModality() {
        return ModalityClass.getNormReprModality(modality);
    }

    public ModelMethod getModelMethod() {
        return meth;
    }

    public SetOfLocationDescriptor getModifies() {
        return spec.getAssignable();
    }

    public String getModifiesText() {
        return LogicPrinter.quickPrintLocationDescriptors(getModifies(), spec.getServices());
    }

    public String getName() {
        return "JML Method Contract: "+spec.getMethodDeclaration().getFullName()+" (spec id:" +spec.id() +")";
    }

    public Object getObjectOfContract() {
        return spec.getProgramMethod();
    }

    public Term getPost() {
        return spec.getCompletePostFunctional(false, false);
    }
  
    public String getPostText() {
        return ProofSaver.printTerm(getPost(), spec.getServices()).toString();
    }

    public Term getPre() {
        return spec.getCompletePre(false, false, modality == Op.DIA);
    }

    public String getPreText() {
        return ProofSaver.printTerm(getPre(), spec.getServices()).toString();
    }


    public ProofEnvironment getProofEnv() {
        return env;
    }


    public ProofOblInput getProofOblInput(Proof proof) {
        return new JMLPostAndInvPO(spec, env.getJavaModel().getModelDir(),
                                   allInvariants); //TODO
    }

    public List getProofs() {
        return proofs;
    }

    public JMLMethodSpec getSpec(){
        return spec;
    }

    public Statement getStatement() {       
        return (Statement) spec.getProofStatement();
    }

    public int hashCode() {
        int result = 0;
        result = 37 * result + meth.hashCode();
        result = 37 * result + getModality().hashCode();
        result = 37 * result + getSpec().hashCode();
        return result;
    }

    
    private static Name getNewName(Services services, Name baseName) {
        NamespaceSet namespaces = services.getNamespaces();
        
        int i = 0;
        Name name;
        do {
            name = new Name(baseName + "_" + i++);
        } while(namespaces.lookup(name) != null);
        
        return name;
    }
    

    protected void instantiateAtPreSymbols(Map replacementMap, Namespace localFunctions, 
            Namespace localProgramVariables) {}

    protected void instantiateAuxiliarySymbols(Map replacementMap, 
            Namespace localFunctions, Namespace localProgramVariables, Services services) {
        IteratorOfQuantifierPrefixEntry it = spec.getOldLVs().iterator();
        while(it.hasNext()) {
            LogicVariable lv = (LogicVariable) it.next().getVariable();
            
            RigidFunction rf = (RigidFunction) spec.getLv2Const().get(lv);
            if(rf != null) {
                Name name = getNewName(services, rf.name());            
                RigidFunction newRf = new RigidFunction(name, 
            	    				    rf.sort(), 
            	    				    rf.argSort());
                localFunctions.add(newRf);
                replacementMap.put(rf, newRf);        	    
            } 
        }
	IteratorOfOperator ito = spec.getOldFuncSymbols().iterator();
        while(ito.hasNext()) {
            Operator op = ito.next();
	    Name name = getNewName(services, op.name());
	    Operator newOp;
	    if(op instanceof RigidFunction){
		RigidFunction rf = (RigidFunction) op;
		newOp = new RigidFunction(name, rf.sort(), rf.argSort());
	    }else{
		LocationVariable lv = (LocationVariable) op;
		newOp = new LocationVariable(new ProgramElementName(
						       name.toString()), 
					               lv.getKeYJavaType());
	    }
	    localFunctions.add(newOp);
	    replacementMap.put(op, newOp);        	    
        }
    }

    /**
     * adds programvariables used as instantiations for the method parameters
     * to the corresponding map
     * @param insts the {@link MethodContractInstantiation} with the concrete instantiation
     * of the method body statement  
     * @param replacementMap the Map with all instantiations 
     */
    protected void instantiateMethodParameters(MethodContractInstantiation insts, 
            Map replacementMap, Namespace localFunctions, Namespace localProgramVariables) {
        for (int i=0; i<insts.getArgumentCount(); i++) {
            replacementMap.put(spec.getParameterAt(i), insts.getArgumentAt(i));
        }
    }
    
    /**
     * @param insts
     * @param replacementMap
     */
    protected void instantiateMethodReceiver(MethodContractInstantiation insts, 
            Map replacementMap, Namespace localFunctions, Namespace localProgramVariables) {        
        if (spec.getSelf() != null) { // otherwise this is a static method call     
            replacementMap.put(spec.getSelf(), 
        	    	       spec.getServices()
        	    	       	   .getTypeConverter()
        	    	       	   .convertToLogicElement(insts.getReceiver()));
        }
    }

    /**
     * @param insts
     * @param replacementMap
     */
    protected void instantiateMethodReturnVariable(MethodContractInstantiation insts, 
            Map replacementMap, Namespace localFunctions, Namespace localProgramVariables) {
        replacementMap.put(spec.getResultVar(), insts.getResult());
    }

    public void removeCompoundProof(ProofAggregate pl) {
        proofs.remove(pl);
    }

    public void setProofEnv(ProofEnvironment env) {
        if (this.env==null) {
            this.env=env;
        } else if (this.env!=env) {
            throw new IllegalStateException("Method Contract may belong to "
                                            +"only one environment.");
        }
    }

    public String toString() {
        return "[JML] context " + meth + (spec == null? "" :
            "\npre: "+spec.getCompletePre(
                    true, allInvariants,
                    modality == Op.DIA)+
                    "\npost: "+spec.getCompletePost(
                            true, allInvariants)+
                            "\nmodifies: " + spec.
                            replaceModelFieldsInAssignable() +
                            "\npi1: "+ ((JMLLemmaMethodSpec)
                                    spec).getPi1() +
                                    "\nmodality: "+modality);
    }

 
}
