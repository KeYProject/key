package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.SymbolReplacer;

public class WorkingSpaceNonRigidOp extends WorkingSpaceOp {

    public static final Name name = new Name("workingSpaceNonRigid");
    private SymbolReplacer pvr;
    
    public WorkingSpaceNonRigidOp(ProgramMethod pm, SymbolReplacer pvr, Sort sort){
        super(pm, sort, new Name(makeName(pm, pvr)));
        this.pvr = pvr;
    }
    
    public int arity() {
        return 0;
    }
    
    public static String makeName(ProgramMethod p, SymbolReplacer pvr){
        return makeNameWithoutSR(p, sortSymbols(pvr)); 
    }
    
    public static String makeNameWithoutSR(ProgramMethod p, String pvr){
        return WorkingSpaceOp.makeNameHelp(p, name.toString())+pvr;       
    }
    
    public static String sortSymbols(SymbolReplacer pvr){
        String pvrString = ""+pvr;
        String[] entries = pvrString.substring(1, pvrString.length()-1).split(", ");
        return buildPVRString(bubbleSortStrings(entries));
    }
    
    private static String buildPVRString(String[] s){
        String result = "{";
        for(int i=0; i<s.length; i++){
            result += s[i]+(i+1<s.length ? ", " : "");
        }
        result+="}";
        return result;
    }
    
    private static String[] bubbleSortStrings(String[] s){
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
    }

    public boolean validTopLevel(Term term) {
        return term.arity() == arity();
    }
    
    public boolean isRigid(Term term){
        return false;
    }
    
    public SymbolReplacer getProgramVariableReplacer(){
        return pvr;
    }
    
    public boolean equals(Object o){
        if(!(o instanceof WorkingSpaceNonRigidOp)) return false;
        return super.equals(o); 
    }
    
    public int hashCode(){
        return 13*getProgramMethod().hashCode()+5;
    }
    
}
