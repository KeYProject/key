package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProofSaver;

public class WorkingSpaceRigidOp extends Op implements IWorkingSpaceOp{
    
    public static final Name name = new Name("workingSpace");
    private final ProgramMethod pm;
    private final Term pre;
    private final Sort sort;
    
    public WorkingSpaceRigidOp(ProgramMethod pm, Sort sort, Term pre, Services services){
        this(pm, sort, pre, new Name(makeName(pm, pre, services)));
    }
    
    protected WorkingSpaceRigidOp(ProgramMethod pm, Sort sort, Term pre, Name name){
        super(name);
        this.pm = pm;
        this.sort = sort;
        this.pre = pre;
    }
    
    public static String makeName(ProgramMethod p, Term pre, Services services){
        return makeNameHelp(p, pre, name.toString(), services); 
    }
    
    protected static String makeNameHelp(ProgramMethod p, Term pre, String name, Services services){
        String result = "\\"+name+"{";
        result += p.getContainerType().getSort()+"::"+p.getName()+"(";
        for(int i=0; i<p.getParameterDeclarationCount(); i++){
            result+=p.getParameterType(i).getSort()+(i<p.getParameterDeclarationCount()-1 ? "," : "");
        }
        result += ")}"+"{"+ProofSaver.printTerm(pre, services, true).toString()+"}";
        return result;      
    }
    
    public int arity() {
        return 0;
    }

    public boolean validTopLevel(Term term) {
        return term.arity() == arity();
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.IWorkingSpaceOp#getProgramMethod()
     */
    public ProgramMethod getProgramMethod() {
        return pm;
    }
    
    public Term getPre(){
        return pre;
    }
    
    public boolean isRigid(Term term){
        return true;
    }
    
    public Sort sort(Term[] t){
        return sort;
    }
    
    public Sort sort(){
        return sort;
    }
    
    public boolean equals(Object o){
        if(!(o instanceof WorkingSpaceRigidOp)) return false;
        WorkingSpaceRigidOp wso = (WorkingSpaceRigidOp) o;
        return wso.getProgramMethod().equals(pm) && wso.getPre().equals(pre);
    }
    
    public int hashCode(){
        return 13*pm.hashCode()+17*pre.hashCode();
    }
    

}
