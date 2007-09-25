package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public class WorkingSpaceOp extends Op{
    
    public static final Name name = new Name("workingSpace");
    private ProgramMethod pm;
//    private Term pre;
    private Sort sort;
    
    public WorkingSpaceOp(ProgramMethod pm, Sort sort/*, Term pre*/){
        this(pm, sort, new Name(makeName(pm)));
    }
    
    protected WorkingSpaceOp(ProgramMethod pm, Sort sort, Name name){
        super(name);
        this.pm = pm;
        this.sort = sort;
    }
    
    public static String makeName(ProgramMethod p){
        return makeNameHelp(p, name.toString()); 
    }
    
    protected static String makeNameHelp(ProgramMethod p, String name){
        String result = "\\"+name+"{";
        result += p.getContainerType().getSort()+"::"+p.getName()+"(";
        for(int i=0; i<p.getParameterDeclarationCount(); i++){
            result+=p.getParameterType(i).getSort()+",";
        }
        result = result.substring(0, result.length()-1);
        result += ")}";
        return result;      
    }
    
    public int arity() {
        return 1;
    }

    public boolean validTopLevel(Term term) {
        if(term.arity() != arity()) {
            return false;
        }
        return term.sub(0).sort() == Sort.FORMULA;
    }

    public ProgramMethod getProgramMethod() {
        return pm;
    }
    
    public boolean isRigid(Term term){
        return true;
    }
    
/*    public Term getPre(){
        return pre;
    }*/
    
    public Sort sort(Term[] t){
        return sort;
    }
    
    public Sort sort(){
        return sort;
    }
    
    public boolean equals(Object o){
        if(!(o instanceof WorkingSpaceOp)) return false;
        WorkingSpaceOp wso = (WorkingSpaceOp) o;
        return wso.getProgramMethod().equals(pm);
    }
    
    public int hashCode(){
        return 13*pm.hashCode();
    }
    

}
