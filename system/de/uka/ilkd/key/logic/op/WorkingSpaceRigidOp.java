package de.uka.ilkd.key.logic.op;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;

public class WorkingSpaceRigidOp extends Op implements IWorkingSpaceOp{
    
    public static final Name name = new Name("workingSpace");
    private final Term methodTerm;
    private final Term pre;
    private final Sort sort;
    
    public WorkingSpaceRigidOp(Term methodTerm, Sort sort, Term pre, Services services){
        this(methodTerm, sort, pre, new Name(makeName(methodTerm, pre, services)));
    }
    
    protected WorkingSpaceRigidOp(Term methodTerm, Sort sort, Term pre, Name name){
        super(name);
        this.methodTerm = methodTerm;
        this.sort = sort;
        this.pre = pre;
    }
    
    public static String makeName(Term m, Term pre, Services services){
        return makeNameHelp(m, pre, name.toString(), services); 
    }
    
    protected static String makeNameHelp(Term m, Term pre, String name, Services services){
        String result = "\\"+name+"{";
        ProgramMethod p = (ProgramMethod) m.op();
        if(!p.isStatic()){
            result+=m.sub(0).sort()+" "+m.sub(0).op().name();
        }
        result+="}{";
        result += p.getContainerType().getSort()+"::"+p.getName()+"(";
        for(int i=p.isStatic()? 0 : 1; i<m.arity(); i++){
            result+=m.sub(i).sort()+" "+m.sub(i).op().name()+(i<m.arity()-1 ? "," : "");
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

    public Term getMethodTerm(Term t) {
        return methodTerm;
    }
    
    public ProgramMethod getProgramMethod(){
        return (ProgramMethod) methodTerm.op();
    }
    
    public Term getPre(){
        return pre;
    }
    
    public Term getSelf(Term t){
        if(!getProgramMethod().isStatic()){
            return methodTerm.sub(0);
        }
        return null;
    }
    
    public ListOfTerm getParameters(Term t){
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        int i = (getProgramMethod().isStatic() ? 0 : 1);
        for(; i<methodTerm.arity(); i++){
            result = result.append(methodTerm.sub(i));
        }
        return result;
    }
    
    public Term getPre(Term self, 
            ListOfTerm params,
            Services services){
        Map<Term, Term> map = new LinkedHashMap<Term, Term>();
        int i=0;
        if(self!=null && getProgramMethod().isStatic()){
            map.put(methodTerm.sub(0), self);
            i++;
        }
        IteratorOfTerm it = params.iterator();
        while(it.hasNext()){
            map.put(methodTerm.sub(i++), it.next());
        }
        OpReplacer or = new OpReplacer(map);
        return or.replace(pre);
    }
    
    public Term getPre(WorkingSpaceRigidOp wsr,
            Services services){
        Map<Term, Term> map = new LinkedHashMap<Term, Term>();
        for(int i=0; i<methodTerm.arity(); i++){
            map.put(methodTerm.sub(i), wsr.methodTerm.sub(i));
        }       
        OpReplacer or = new OpReplacer(map);
        return or.replace(pre);
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
        return wso.getMethodTerm(null).equals(methodTerm) && wso.getPre().equals(pre);
    }
    
    public int hashCode(){
        return 13*methodTerm.hashCode()+17*pre.hashCode();
    }
    

}
