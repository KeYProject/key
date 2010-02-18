package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.sort.Sort;

public class WorkingSpaceNonRigidOp extends NonRigidFunction implements IWorkingSpaceOp{

    public static final Name name = new Name("workingSpaceNonRigid");
    private final ProgramMethod pm;
    private final Sort sort;
    
    public WorkingSpaceNonRigidOp(ProgramMethod pm, Sort sort){
        super(new Name(makeName(pm)), sort, pm.argSort());
        this.pm = pm;
        this.sort = sort;
    }
    
    public int arity() {
        return pm.arity();
    }
    
    public static String makeName(ProgramMethod pm){
        return "\\"+name+"{"+pm.getContainerType().getSort()+"::"+pm.getName()+"}";
    }
    
/*    public static String makeNameWithoutSR(ProgramMethod p, String pvr){
        String result = "\\"+name+"{";
        result += p.getContainerType().getSort()+"::"+p.getName()+"(";
        for(int i=0; i<p.getParameterDeclarationCount(); i++){
            result+=p.getParameterType(i).getSort()+(i<p.getParameterDeclarationCount()-1 ? "," : "");
        }
        result += ")}";
        return result+pvr;  
    }*/
    
/*    public static String sortSymbols(SymbolReplacer pvr){
        String pvrString = ""+pvr;
        String[] entries = pvrString.substring(1, pvrString.length()-1).split(", ");
        return buildPVRString(bubbleSortStrings(entries));
    }*/
    
    private static String buildPVRString(String[] s){
        String result = "{";
        for(int i=0; i<s.length; i++){
            result += s[i]+(i+1<s.length ? ", " : "");
        }
        result+="}";
        return result;
    }
    
    /*private static String[] bubbleSortStrings(String[] s){
        boolean sorted = false;
        while(!sorted){
            sorted = true;
            for(int i=0; i<s.length-1; i++){
                if(s[i].compareTo(s[i+1].toString())>0){
                    String temp = s[i];
                    s[i] = s[i+1];
                    s[i+1] = temp;
                    sorted = false;
                }
            }
        }
        return s;
    }*/

    public boolean validTopLevel(Term term) {
        return term.arity() == pm.getParameterDeclarationCount()+(pm.isStatic() ? 0 : 1);
    }
    
    public boolean isRigid(Term term){
        return false;
    }
    
  /*  public SymbolReplacer getProgramVariableReplacer(){
        return pvr;
    }*/
    
    public Sort sort(Term[] t){
        return sort;
    }
    
    public Sort sort(){
        return sort;
    }
    
    public Term getMethodTerm(Term t) {
        return null;
    }
    
    public ProgramMethod getProgramMethod(){
        return pm;
    }
    
    public boolean equals(Object o){
        if(!(o instanceof WorkingSpaceNonRigidOp)) return false;
        return super.equals(o); 
    }
    
    public int hashCode(){
        return 13*pm.hashCode()+5;
    }

    public ImmutableList<Term> getParameters(Term t) {
        assert t.op() == this;
        ImmutableList<Term> result = new ImmutableList<Term>();
        int i = (getProgramMethod().isStatic() ? 0 : 1);
        for(; i<t.arity(); i++){
            result = result.append(t.sub(i));
        }
        return result;
    }

    public Term getSelf(Term t) {
        assert t.op() == this;
        if(!pm.isStatic()){
            return t.sub(0);
        }
        return null;
    }
    
}
