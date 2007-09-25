package de.uka.ilkd.key.rule;

import java.util.Iterator;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.IteratorOfKeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.mgt.*;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.IteratorOfClassInvariant;
import de.uka.ilkd.key.speclang.SLTranslationError;

/**
 * implements the rule which inserts method contracts for a method body
 * statement
 * 
 * @author andreas
 * 
 */
public class UseMethodContractRule implements BuiltInRule {

    private final Name name = new Name("Use Method Contract");
    private final TermBuilder tb = TermBuilder.DF;
  
    
    /** The only instance of this rule */
    public static UseMethodContractRule INSTANCE = new UseMethodContractRule();

    protected UseMethodContractRule() {
    }
    
    /**
     * returns true iff this rule is applicable at the given position, that is,
     * if there is a contract applicable for a method body statement at that
     * position in the specification repository belonging to the proof of the
     * given goal. This does not necessarily mean that a rule application will
     * change the goal (this decision is made due to performance reasons)
     */
    public boolean isApplicable(Goal goal, PosInOccurrence pos, 
                                Constraint userConstraint) {
        final Services services = goal.node().proof().getServices();
        final MbsInfo mbsInfo = getMbsInfo(pos);
       
        return mbsInfo != null && getContracts(mbsInfo.mbs.getProgramMethod(services), 
                mbsInfo.modality, services, goal.proof(), pos).size() != 0;
    }
    
    /**
     * returns the list of all program methods overriden 
     * by the given method <tt>pm</tt> inclusive <tt>pm</tt>
     * @param pm the ProgramMethod 
     * @param services the Services 
     * @return list of all overridden methods
     */
    private ListOfProgramMethod getProgramMethodsInSupertypes
    (ProgramMethod pm, Services services) {
        final IteratorOfKeYJavaType types = 
            services.getJavaInfo().getAllSupertypes(pm.getContainerType()).iterator();
        
        ListOfProgramMethod allMethods = SLListOfProgramMethod.EMPTY_LIST;
        while (types.hasNext()) {
            if (!(types instanceof ArrayType)) {
                allMethods = allMethods.prepend
                (services.getJavaInfo().getAllProgramMethodsLocallyDeclared
                        (types.next()));
            }
        }

        final String pmName = pm.getMethodDeclaration().getName();
        
        ListOfProgramMethod result = SLListOfProgramMethod.EMPTY_LIST;
        final IteratorOfProgramMethod it = allMethods.iterator();
        nextOverriddenMethod: while (it.hasNext()) {
            final ProgramMethod p = it.next();
            if (p != pm
                    && p.getMethodDeclaration().getName().equals(pmName)
                    && p.getParameterDeclarationCount() == pm
                            .getParameterDeclarationCount()) {
                for (int i = 0; i < p.getParameterDeclarationCount(); i++) {
                    if (p.getParameterDeclarationAt(i).getTypeReference()
                            .getKeYJavaType() != pm
                            .getParameterDeclarationAt(i).getTypeReference()
                            .getKeYJavaType()) {
                        continue nextOverriddenMethod;
                    }
                }
                result = result.prepend(p);
            }
        }
        return result.prepend(pm); 
    }
    
    private static MbsInfo getMbsInfo(PosInOccurrence pio) {
        if (pio==null || pio.isInAntec()) {
            return null;
        }
        
	Term t = pio.subTerm();        
	
        while (t.op() instanceof IUpdateOperator) {
            pio = pio.down(((IUpdateOperator)t.op()).targetPos());
            t = pio.subTerm();
        }

        if (!(t.op() instanceof Modality)) {
            return null;
        }

        final Modality modality = (Modality) t.op(); 
        final ProgramElement pe = t.executableJavaBlock().program();        

        if (pe == null) { // TODO: can this situation occurr? 
            return null;
        }

        PosInProgram res = PosInProgram.TOP;
        ProgramElement activeStatement = (Statement) pe;
        ExecutionContext ec = null;
	
        if (activeStatement instanceof ProgramPrefix) {

	    ProgramPrefix curPrefix = (ProgramPrefix)activeStatement;

	    final ArrayOfProgramPrefix prefix = curPrefix.getPrefixElements();
	    final int length = prefix.size();
	    
	    // fail fast check	    
	    curPrefix = prefix.getProgramPrefix(length-1);// length -1 >= 0 as prefix array 
	                                                  //contains curPrefix as first element

	    activeStatement = curPrefix.getFirstActiveChildPos().getProgram(curPrefix);

	    if (!(activeStatement instanceof MethodBodyStatement)) {
		return null;
	    }
	
	    int i = length - 1;
	    do {
		if (ec == null && curPrefix instanceof MethodFrame) {
		    ec = (ExecutionContext)((MethodFrame)curPrefix).getExecutionContext(); 
		}
		res = curPrefix.getFirstActiveChildPos().append(res);
		i--;
		if (i >= 0) {
		    curPrefix = prefix.getProgramPrefix(i);
		}
	    } while (i >= 0); 	    

        } else if (!(activeStatement instanceof MethodBodyStatement)) {
	    return null;
	} 
        return new MbsInfo(pio, res, ec, (MethodBodyStatement)activeStatement, modality);
    }

    
    /**
     * return the set of all contracts for the given method (including
     * the contracts of possible overriden methods) and termination marker
     * @param pm the ProgramMethod whose contracts are collected
     * @param modality the Modality serving as termination marker
     * @param services the Services
     * @return all contracts applicable for the given method 
     */
    private ContractSet getContracts(ProgramMethod pm, 
                                     Modality modality, 
                                     Services services,
                                     Proof proof,
                                     PosInOccurrence pos) {   
        
        ContractSet ctSet = new ContractSet();
        IteratorOfProgramMethod it = getProgramMethodsInSupertypes(pm, services).iterator();
        while (it.hasNext()) {
            ContractSet contracts = services.getSpecificationRepository().getContract(it.next(), modality);
            
            //prevent application of contracts with "everything" modifier sets 
            //if metavariables are involved (hackish, see Bug 810)
            if(getAllMetavariables(pos.topLevel().subTerm()).size() > 0) {
                Iterator it2 = contracts.iterator();
                while(it2.hasNext()) {
                    OldOperationContract ct = (OldOperationContract) it2.next();
                    if(ct.createDLMethodContract(proof).getModifies().contains(EverythingLocationDescriptor.INSTANCE)) {
                        it2.remove();
                    }
                }
            }
            
            ctSet.addAll(contracts);
        }
        return ctSet;
    }
    
    /**
     * calls the given contract configurator and returns the selected contract
     * or creates a new DLMethodContract from the results of the
     * configuration. The selected / configured contract suits to the given
     * position. It is added to the proof environment of the given proof.
     * 
     */
    private OldOperationContract selectContract(Services services, 
                                          Proof proof, 
                                          PosInOccurrence pos, 
                                          ContractConfigurator cc,
                                          boolean allowConfiguration) {
        final SpecificationRepository repos 
            = services.getSpecificationRepository();
        MbsInfo mbsPos = getMbsInfo(pos);
        MethodBodyStatement mbs = mbsPos.mbs;
        Modality modality = mbsPos.modality;
        ProgramMethod pm = mbs.getProgramMethod(services);                
        ContractSet ctSet = getContracts(pm, modality, services, proof, pos);
        if (ctSet.size()==0) {
            return null;
        }
        cc.setSpecification(repos);
        cc.setProgramMethods(getProgramMethodsInSupertypes(pm, services));
        cc.setModality(modality);
        cc.allowConfiguration(allowConfiguration);
        cc.start(); 
        if (!cc.wasSuccessful()) return null;
        DLMethodContract dlhResultCt = null;
	    if (cc.getPreInvariants().isEmpty() 
	            && cc.getPostInvariants().isEmpty()) {
	        return cc.getMethodContract();
	    } else {
	        dlhResultCt = 
	            cc.getMethodContract().createDLMethodContract(proof);
	        
	        IteratorOfClassInvariant it = cc.getPreInvariants().iterator();
	        while (it.hasNext()) {
	        	try {
	                dlhResultCt.addPre(it.next().getInv(services).getFormula()); 
	        	} catch (SLTranslationError e) {
	        		// too bad (error in invariant)
	        		// TODO:
	        		// user should be informed about what happend here!
	        	}
	      	}
	        it = cc.getPostInvariants().iterator();
	        while (it.hasNext()) {
	            try {
	            	dlhResultCt.addPost(it.next().getInv(services).getFormula()); 
	            } catch (SLTranslationError e) {
	            	// too bad (error in invariant)
	            	// TODO:
	            	// user should be informed about what happend here!
	            }
	        }
	        dlhResultCt = (DLMethodContract) proof.env().addMethodContract(dlhResultCt);
	    }


        return dlhResultCt;
    }
    
    /**
     * calls the given contract configurator and returns the selected contract
     * or creates a new DLMethodContract from the results of the
     * configuration. The selected / configured contract suits to the given
     * position. It is added to the proof environment of the given proof.
     * 
     */
    public OldOperationContract selectContract(Proof proof, PosInOccurrence pos, 
                                         ContractConfigurator cc) {
        return selectContract(proof.getServices(), proof, pos, cc, true);
    }
    
    /**
     * calls the given contract configurator and returns the selected contract
     * or creates a new DLMethodContract from the results of the
     * configuration. The selected / configured contract suits to the given
     * position. It is added to the proof environment of the given proof.
     * 
     */
    public OldOperationContract selectExistingContract(Services services, 
                                                 PosInOccurrence pos, 
                                                 ContractConfigurator cc) {
        return selectContract(services, null, pos, cc, false);
    }
    
    
    private OldOperationContract getSelectedMethodContract(RuleApp ruleApp, Proof proof) {        
        if (ruleApp instanceof MethodContractRuleApp) {
            // selected beforehand
            return ((MethodContractRuleApp) ruleApp).getMethodContract();    
        }
        return selectContract(proof, ruleApp.posInOccurrence(), 
                              AutomatedContractConfigurator.INSTANCE);
    }
    
    private static ProgramElementName getNewName(Services services, String baseName) {
        NamespaceSet namespaces = services.getNamespaces();
        
        int i = 0;
        ProgramElementName name;
        do {
            name = new ProgramElementName(baseName + "_" + i++);
        } while(namespaces.lookup(name) != null);
        
        return name;
    }
    

    /**
     * the rule is applied based on the information of the given rule application: 
     * if the given rule application is a 
     * {@link MethodContractRuleApp} then the contained method contract is applied, 
     * otherwise a contract is selected based on the 
     * {@link AutomatedContractConfigurator}.
     * @param goal the goal that the rule application should refer to
     * @param services the Services with the necessary information about 
     *        the java programs
     * @param ruleApp the rule application that is executed.
     */
    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {
        OldOperationContract ct = getSelectedMethodContract(ruleApp, goal.node().proof());
        
        MbsInfo mbsPos = getMbsInfo(ruleApp.posInOccurrence());
        MethodBodyStatement mbs = mbsPos.mbs;
        Modality modality = mbsPos.modality;
        
        Expression[] insts = new Expression[mbs.getArguments().size()];
        mbs.getArguments().arraycopy(0,insts,0,mbs.getArguments().size());        
        Expression receiver = null;
        if (mbs.getDesignatedContext() instanceof Expression) {
            receiver = (Expression) mbs.getDesignatedContext(); 
        }        
        
        ProgramVariable resultVar = (ProgramVariable) mbs.getResultVariable();
        ProgramMethod pm = mbs.getProgramMethod(services);
        if(resultVar == null && pm.getKeYJavaType() != null) {
            //method is non-void, but its result is discarded; we need to create a 
            //result variable anyway
            ProgramElementName pen = getNewName(services, "res");
            resultVar = new LocationVariable(pen, pm.getKeYJavaType());
            services.getNamespaces().programVariables().add(resultVar);
        }
        
        MethodContractInstantiation mci 
            = new MethodContractInstantiation(receiver, insts, 
                    resultVar, modality);
        final InstantiatedMethodContract ctInst = 
            ct.instantiate(mci, goal.node().proof()); 
        
        if (ctInst == null) {            
            return SLListOfGoal.EMPTY_LIST.prepend(goal.split(1));
        }
        
        return applyInstantiatedContract(goal, ruleApp.posInOccurrence(), 
                ctInst, mbsPos, services);
    }
    
    
    
    /**
     * executes the instantiated method contract and returns the newly created goals
     * @param goal the Goal where the method contract rule has been applies
     * @param pos the PosInOccurunce describing the rules focus
     * @param iCt the InstantiatedMethodContract
     * @param mbsPos information about the method body statement on which the rule matched
     * @param services the Services
     * @return the new goals created by applying the method contract rule 
     */
    private ListOfGoal applyInstantiatedContract(Goal goal, PosInOccurrence pos, 
            InstantiatedMethodContract iCt, 
            MbsInfo mbsPos, Services services) {
     
        services.getNamespaces().functions().add(iCt.getAdditionalFunctions());

        final UpdateFactory uf = new UpdateFactory(services, goal.simplifier());
        final Update u = updateToRigid(iCt, uf, services, pos);       
        
        final boolean openExceptionalBranch = iCt.getExceptionVariable() != null;                                                
        
        final ListOfGoal result = 
            (openExceptionalBranch ? goal.split(3) : goal.split(2));            
               
        final IteratorOfGoal goalIt = result.iterator();

        if (openExceptionalBranch) {        
            openBranch(pos, iCt, mbsPos, excPostFma(iCt, mbsPos, uf, u, services), 
                    goalIt.next(), getExceptionalLabel(), services);                     
        }
 
        openBranch(pos, iCt, mbsPos, postFma(iCt, mbsPos, uf, u, services), 
                goalIt.next(), getPostLabel() ,services);
    	       
 
        openBranch(pos, iCt, mbsPos, preFma(iCt, mbsPos, uf, u, services), 
                goalIt.next(), getPreLabel(), services);        
        return result;
    }

    /**
     * opens a new branch with branch label <code>branchLabel</code>, replaces 
     * the formula the rule has in focus (described by <code>mbsPos</code>) by formula
     * <code>newFormula</code>
     * @param pos the Position of the focus term
     * @param iCt the InstantiatedMethodContract
     * @param mbsPos position of the method body statement (the one in focus of the rule)
     * @param newFormula the Term with the new formula 
     * @param branchGoal the new Goal where to replace the formula
     * @param branchLabel a String labelling the branch
     * @param services the Services
     */
    private void openBranch(PosInOccurrence pos, InstantiatedMethodContract iCt,
            MbsInfo mbsPos, final Term newFormula, final Goal branchGoal, String branchLabel, 
            Services services) {
        branchGoal.node().getNodeInfo().setBranchLabel(branchLabel);
        replaceFormula(mbsPos.pio, branchGoal, newFormula);            
        addAdditionalProgramVariables(iCt, pos, branchGoal, services);
    }

    /**
     * adds and renames if necessary the newly introduced program variables to 
     * the given goal
     * @param iCt the InstantiatedMethodContract containing a set of all newly added
     * program variables
     * @param pos the PosInOccurrence of the find focus
     * @param goal the Goal 
     * @param services the Services
     */
    private void addAdditionalProgramVariables(InstantiatedMethodContract iCt, 
            PosInOccurrence pos, Goal goal, Services services) {
        final IteratorOfNamed it = 
            iCt.getAdditionalProgramVariables().allElements().iterator();
        while (it.hasNext()) {
            final ProgramVariable next = (ProgramVariable) it.next();
            assert !next.isMember();
            final ProgramVariable renamed = 
                services.getVariableNamer().rename(next, goal, pos);          
            goal.addProgramVariable(renamed);
        }
    }
    
    /**
     * replace the formula at position <tt>pio</tt> of goal <tt>g</tt> 
     * by the new formula <tt>fma</tt>
     * @param pio the PosInOccurrence of the formula to be replaced
     * @param g the Goal where to replace the formula
     * @param fma the Term that is the new formula
     */
    private void replaceFormula(PosInOccurrence pio, Goal g, Term fma) {
        final ConstrainedFormula cf = pio.constrainedFormula();
        final ConstrainedFormula newCf = new ConstrainedFormula
            (replace(cf.formula(), fma, pio.posInTerm().iterator()), cf.constraint()); 
        g.changeFormula(newCf, pio);
    }
    
    private Term replace(Term term, Term with, IntIterator it) {        
        if (it.hasNext()) {         
            int sub = it.next();
            Term[] subs=new Term[term.arity()];
            final ArrayOfQuantifiableVariable[] vars = 
                new ArrayOfQuantifiableVariable[term.arity()];        
            for (int i=0;i<term.arity();i++) {
                if (i!=sub) {
                    subs[i]=term.sub(i);
                } else {
                    subs[i]=replace(term.sub(i), with, it);
                }
                vars[i] = term.varsBoundHere(i);
            }

            return TermFactory.DEFAULT.createTerm(term.op(), subs, vars,
                    term.javaBlock());          
        }
        return with;
    }
    
    protected String getPreLabel() {
        return "Pre";
    }
    
    protected Term preFma(InstantiatedMethodContract iCt, 
                MbsInfo mbsPos, UpdateFactory uf, 
                Update u, Services services) {
        return iCt.getPre();
    }    
    
    protected String getPostLabel() {
        return "Post";
    }
    protected Term postFma(InstantiatedMethodContract iCt, 
                         MbsInfo mbsPos, UpdateFactory uf, 
                         Update u, Services services) {
        StatementBlock methodReplaceStatements = new StatementBlock();
        Term extraPre;
        if (iCt.getExceptionVariable()!=null) {           
            extraPre = tb.equals(tb.var(iCt.getExceptionVariable()), tb.NULL(services));
        } else {
            extraPre = tb.tt();
        }
        extraPre = tb.and(extraPre, iCt.getAtPreAxioms());        
        return postFmaHelp(iCt, mbsPos, uf, u, methodReplaceStatements, extraPre);
    }
    
    protected String getExceptionalLabel() {
        return "Exceptional Post";
    }
    
    protected Term excPostFma(InstantiatedMethodContract iCt, MbsInfo mbsPos, 
                            UpdateFactory uf, Update u, Services services) {
            
        final StatementBlock methodReplaceStatements 
            = new StatementBlock(new Throw(iCt.getExceptionVariable()));
        final Term extraPre = 
            tb.and(
            		tb.not(tb.equals(tb.var(iCt.getExceptionVariable()), tb.NULL(services))),
            		iCt.getAtPreAxioms());                
        return postFmaHelp(iCt, mbsPos, uf, u, methodReplaceStatements, extraPre);
    }
    
    private Term postFmaHelp(InstantiatedMethodContract iCt, MbsInfo mbsPos, 
                             UpdateFactory uf, Update u, StatementBlock methodReplaceStmts, 
                             Term extraPre) {
        JavaNonTerminalProgramElement all 
        = (JavaNonTerminalProgramElement)mbsPos.pio.subTerm().javaBlock().program();     
        NonTerminalProgramElement npe = replaceStatement(all, mbsPos, methodReplaceStmts);
        Term restFma = tb.tf().createProgramTerm(iCt.getModality(), 
                                            JavaBlock.createJavaBlock((StatementBlock)npe), 
                                            mbsPos.pio.subTerm().sub(0));        
        
        restFma = uf.apply(u, restFma);
        final Term methodReplacement = tb.and(tb.and(extraPre, iCt.getPre()), 
                uf.apply(u, iCt.getPost()));        
        return tb.imp(methodReplacement, restFma);
    }
    
    protected NonTerminalProgramElement replaceStatement(JavaNonTerminalProgramElement all, 
						       MbsInfo mbsPos, 
						       StatementBlock with) {
	int lastPos = mbsPos.pos.last();
        ContextStatementBlockInstantiation csbi = 
	    new ContextStatementBlockInstantiation(mbsPos.pos, 
						   mbsPos.pos.up().down(lastPos+1), 
						   mbsPos.execContext, all);     
        final NonTerminalProgramElement npe = 
	    ProgramContextAdder.INSTANCE.start(all, with, csbi);
        return npe;
    }
    
    
    private SetOfMetavariable getAllMetavariables(Term term) {
        SetOfMetavariable result = SetAsListOfMetavariable.EMPTY_SET;
        
        if(term.op() instanceof Metavariable) {
            result = result.add((Metavariable) term.op());
        }
        
        for(int i = 0; i < term.arity(); i++) {
            result = result.union(getAllMetavariables(term.sub(i)));
        }
        
        return result;
    }
    
    
    private Update updateToRigid(InstantiatedMethodContract iCt, UpdateFactory uf, 
                                 Services services, PosInOccurrence pio) {
        SetOfMetavariable mvs = getAllMetavariables(pio.topLevel().subTerm());
        Term[] mvTerms = new Term[mvs.size()];
        IteratorOfMetavariable it = mvs.iterator();
        for(int i = 0; i < mvTerms.length; i++) {
            mvTerms[i] = TermBuilder.DF.func(it.next());
        }
        
        AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
        return auf.createAnonymisingUpdate(iCt.getModifies(), mvTerms, services);
    }
  
    /**
     * returns the name of this rule
     */
    public Name name() {
        return name;
    }

    /**
     * returns the display name of this rule
     */
    public String displayName() { 
        return name.toString();
    }
    
    /**
     * toString
     */
    public String toString() {
        return displayName();
    }

    /**
     * A helper container class to store information on a method body statement 
     * @author andreas
     *
     */
    protected static class MbsInfo {
        public PosInProgram pos;
        public ExecutionContext execContext;
        public MethodBodyStatement mbs;
        public Modality modality;
        public PosInOccurrence pio;
        
        public MbsInfo(PosInOccurrence pio, PosInProgram pos, ExecutionContext ec, 
                       MethodBodyStatement mbs, Modality mod) {
            this.pos=pos;
            this.execContext=ec;
            this.mbs=mbs;
            this.modality=mod;
            this.pio=pio;
        }
    }
    
}
