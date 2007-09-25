package de.uka.ilkd.key.visualdebugger;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.NullType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;

public class SymbolicObject {
    
    private final SetOfTerm terms;
    private final ClassType type;
    VisualDebugger vd=VisualDebugger.getVisualDebugger();
   
    private final HashMap associations = new HashMap();
    private final HashMap attr2Constraint = new HashMap();

    private  boolean unknownObject=false;
    private ProgramMethod method=null;
    private ListOfProgramVariable parameter;

    private HashMap par2value= new HashMap();
    private HashMap par2constraint= new HashMap();
   
    
    private HashMap attr2ValueTerm = new HashMap();
private int id;
private boolean isStatic=false;
private String instanceName;

    

    public SymbolicObject(SetOfTerm cl, ClassType t,Services s){
        this.terms=cl;   
        assert cl!=null && t !=null && s!=null;
        type = t;
        computeInstanceName();
    }
    
    
    
    
    public SymbolicObject(Term cl, ClassType t,Services s){
        this(SetAsListOfTerm.EMPTY_SET.add(cl),t,s);
    }
    
    public SymbolicObject(Term cl, ClassType t,Services s, boolean unKnown){
        this(SetAsListOfTerm.EMPTY_SET.add(cl),t,s);
        this.unknownObject=unKnown;
    }
    
    
    public SymbolicObject(ClassType t, Services s){    
        this.type=t;
        this.terms=SetAsListOfTerm.EMPTY_SET;
        this.isStatic = true;
        this.computeInstanceName();
    }


    
    public ClassType getType(){
        return type;
    }
    
    
    
    public boolean isNull(){
        return (type instanceof NullType);
    }
    
    public void addAttributeConstraint(ProgramVariable f, Term o){    
        if (attr2Constraint.containsKey(f)){
            ListOfTerm t = (ListOfTerm)attr2Constraint.get(f);
            t = t.append(o);
            attr2Constraint.remove(f);
            attr2Constraint.put(f, t);
            
        }else{
            ListOfTerm t = SLListOfTerm.EMPTY_LIST.append(o);            
            attr2Constraint.put(f, t);
        }
      
        
    }
    
    
    public void addParameterConstraint(ProgramVariable f, Term o){    
        if (this.par2constraint.containsKey(f)){
            ListOfTerm t = (ListOfTerm)par2constraint.get(f);
            t = t.append(o);
            par2constraint.remove(f);
            par2constraint.put(f, t);
        }else{
            ListOfTerm t = SLListOfTerm.EMPTY_LIST.append(o);            
            par2constraint.put(f, t);
        }
    }

    
    public void addParameterConstraint(ProgramVariable f, ListOfTerm o){    
        if (this.par2constraint.containsKey(f)){
            ListOfTerm t = (ListOfTerm)par2constraint.get(f);
            t = t.append(o);
            par2constraint.remove(f);
            par2constraint.put(f, t);
        }else{
            ListOfTerm t = SLListOfTerm.EMPTY_LIST.append(o);            
            par2constraint.put(f, t);
        }
    }
    
    
    public void addAssociation(IProgramVariable f, SymbolicObject o){
        associations.put(f, o);
        
    }
      
    
    public SetOfProgramVariable getAttributes(){
        SetOfProgramVariable result=SetAsListOfProgramVariable.EMPTY_SET;
        Set s = attr2Constraint.keySet();
        for(Iterator it= s.iterator();it.hasNext();){
            result = result.add((ProgramVariable)it.next());
        }
        return result;
    }
    
    
    public ListOfTerm getAttrConstraints(ProgramVariable f){      
        return (ListOfTerm)attr2Constraint.get(f);
    }
     
    
    public ListOfTerm getParaConstraints(ProgramVariable f){      
        return (ListOfTerm)this.par2constraint.get(f);
    }
 
    
    public SetOfProgramVariable getNonPrimAttributes(){
        SetOfProgramVariable result=SetAsListOfProgramVariable.EMPTY_SET;
        Set s = associations.keySet();
        for(Iterator it= s.iterator();it.hasNext();){
            result = result.add((ProgramVariable)it.next());
        }
        return result;
    }
    
    
  
    public SymbolicObject getAssociationEnd(ProgramVariable f){
        return (SymbolicObject)associations.get(f);
    }

    
    
    public String toString(){
        String result="Symbolic Object "+this.instanceName+" ";
        result += "Members "+terms;
        
        return result;
        
    }
    
   
        
    

    public SetOfTerm getTerms(){
        return terms;
    }

    
    
      
    
    public String getInstanceName(){
        return this.instanceName;
    }
    
    
    
    private void computeInstanceName() {
        if (isStatic()) {
            this.instanceName = "<Class>";

        } else if (!vd.isStaticMethod()&&terms.contains((Term) VisualDebugger
                .getVisualDebugger().getInputPV2term().get(
                        vd.getSelfTerm()))) {
            this.instanceName = "self";

        } else if (id==-1){
            
            
        }
        
        else {
            final String className = getType().getName().toString();
            final String b = className.substring(0, 1).toLowerCase();
            instanceName = b + className.substring(1, className.length());
            instanceName += "_" + id;
        }
    }

    
    
    
    
    
    
    

//    public void setName(String name) {
//        this.name = name;
//    }
//    
    public void setId(int id){
        this.id = id;
        this.computeInstanceName();
    }
    
    public int getId(){
        return id;
    }
    
    public Collection getAllAssociationEnds(){        
        return this.associations.values();
        
    }
    
    
    //------------------------------------------------------------------
    // Methods for post state
    
    public void addValueTerm(ProgramVariable pv, Term val){
        attr2ValueTerm.put(pv, val);        
    }
    
    public SetOfProgramVariable getAllModifiedPrimitiveAttributes(){
        SetOfProgramVariable result=SetAsListOfProgramVariable.EMPTY_SET;
        Set s = attr2ValueTerm.keySet();
        for(Iterator it= s.iterator();it.hasNext();){
            result = result.add((ProgramVariable)it.next());
        }
        return result;
    }
    
    public Term getValueTerm(ProgramVariable pv){
        return (Term) this.attr2ValueTerm.get(pv);
    }

    public boolean isUnknownObject() {
        return unknownObject;
    }




    public boolean isStatic() {
        return isStatic;
    }




    public ProgramMethod getMethod() {
        return method;
    }




    public void setMethod(ProgramMethod method) {
        this.method = method;
    }




    public ListOfProgramVariable getParameter() {
        return parameter;
    }




    public void setParameter(ListOfProgramVariable parameter) {
        this.parameter = parameter;
    }

    /**
     * 
     * @param par parameter pv
     * @param value instanceof SymbolicObject or Term
     */
    public void addPara2Value(ProgramVariable par, Object value){
        this.par2value.put(par, value);
    }
    
    /**
     * 
     * @param para
     * @return instanceof SymbolicObject or Term
     */
    public Term getValueOfParameter(ProgramVariable para){
        return (Term)par2value.get(para);
        
    }
    
    
    
}
