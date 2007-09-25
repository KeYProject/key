
package de.uka.ilkd.key.visualdebugger;

import java.util.*;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayOfParameterDeclaration;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.unittest.ModelGenerator;


public class SymbolicObjectDiagram {
    private SetOfTerm locations = SetAsListOfTerm.EMPTY_SET;
    private ListOfTerm ante=SLListOfTerm.EMPTY_LIST, succ=SLListOfTerm.EMPTY_LIST;
    private HashMap term2class;
    private ITNode itNode;
    private Node node;
    private Services serv;
    private static Term nullTerm = 
        TermFactory.DEFAULT.createFunctionTerm(Op.NULL);

    private SetOfTerm refInPC = SetAsListOfTerm.EMPTY_SET; 
    ListOfTerm pc=SLListOfTerm.EMPTY_LIST;

    LinkedList terms = new LinkedList();
    private LinkedList symbolicObjects;
    private HashMap ref2ser;
    private VisualDebugger vd;

    private ListOfTerm postTerms;

    private  SetOfTerm indexTerms;
    private  SetOfTerm arrayLocations;
    private SetOfTerm instanceConfiguration;
    private Term methodReferences[];
    private SetOfTerm[] possibleIndexTerms;




    private void prepare( ITNode itNode, Services serv, ListOfTerm pc,
            SetOfTerm refInPc) {

        this.vd = VisualDebugger.getVisualDebugger();
        this.pc = pc;
        //this.node = n;
        this.node= itNode.getNode();
        this.itNode = itNode;
        // this.mediator=mediator;
        // mediator = Main.getInstance().mediator();
        this.serv = serv;
        // goals = mediator.getProof().getSubtreeGoals(node);

        VisualDebugger.print("--------------------------");
        VisualDebugger.print("Calculating Equ classes for " + node.serialNr());

        IteratorOfConstrainedFormula itc = node.sequent().antecedent()
        .iterator();
        while (itc.hasNext()) {
            ante = ante.append(itc.next().formula());
        }
        itc = node.sequent().succedent().iterator();
        succ = SLListOfTerm.EMPTY_LIST;
        while (itc.hasNext()) {
            succ = succ.append(itc.next().formula());
        }

        for(IteratorOfTerm it = this.instanceConfiguration.iterator();it.hasNext();){
            final Term t = it.next();
            if (t.op() == Op.NOT)
                succ = succ.append(t.sub(0));
            else ante = ante.append(t);            
        }

        this.refInPC = refInPc;


        createEquivalenceClassesAndConstraints();
        getEqvClass(nullTerm);
        findDisjointClasses();

        Collection cl = term2class.values();
        HashSet s = new HashSet(cl);
        Iterator it5 = s.iterator();
        VisualDebugger.print("All Equi Classses: ");
        while (it5.hasNext())
            VisualDebugger.print(it5.next());
    }





    public SymbolicObjectDiagram( ITNode itNode, Services serv, ListOfTerm pc, SetOfTerm refInPC,  
            ListOfTerm preTerms, ListOfTerm postTerms, boolean pre, SetOfTerm arrayLocations,SetOfTerm[] possibleIndexTerms,
            SetOfTerm indexTerms, SetOfTerm instanceConfiguration){
        this.instanceConfiguration =instanceConfiguration; 
        prepare(itNode, serv, pc,refInPC);           
        this.postTerms=postTerms;

        this.arrayLocations = arrayLocations;

        this.possibleIndexTerms= possibleIndexTerms;


        this.indexTerms=  indexTerms;

        createSymbolicObjects();
        if (!pre){
            createSymbolicObjectsForNewInstances(preTerms);
            createPostState(preTerms, postTerms);
            setMethodStack(pre);
        }

        setInstanceNames(symbolicObjects);
    }





    private void setMethodStack(boolean pre) {
        try{
            ITNode it = itNode.getMethodNode(); 
            if (it==null){
                return;
            }


            MethodBodyStatement mbs = //vd.getLastMethodBodyStatement(itNode.getNode());
                (MethodBodyStatement)it.getActStatement();
            // MethodBodyStatement mbs = vd.getLastMethodBodyStatement(itNode.getNode());
            if (mbs==null)
                return;
            ReferencePrefix refPre = mbs.getMethodReference().getReferencePrefix(); 
            SymbolicObject so;

            if (refPre instanceof TypeRef){
                final KeYJavaType kjt = ((TypeRef)refPre).getKeYJavaType();
                final ClassType type = (ClassType)kjt.getJavaType();
                so = getStaticObject(type, symbolicObjects);
                if (so ==null){
                    so = new SymbolicObject(type,serv);
                    symbolicObjects.add(so);
                }


                so.setMethod(mbs.getProgramMethod(serv));

            }else{


                final Term t = serv.getTypeConverter().convertToLogicElement(refPre);
                methodReferences = new Term[1];
                methodReferences[0]=t;
                //System.out.println("AAAAAAAAAAAAAAAAAAAAAA  "+t);
                HashMap map = new HashMap();
                Term self = vd.getSelfTerm();
                //   vd.getSelfTerm()           //TODO
                //   ProgramVariable val = (ProgramVariable)((Term)vd.getInputPV2term().get(self)).op();
                Term val = ((Term)vd.getInputPV2term().get(self));
                map.put(self.op(), val);
                ProgVarReplacer pvr = new ProgVarReplacer(map);
                Term res = pvr.replace(t);

                so = getObject(res, symbolicObjects);
                so.setMethod(mbs.getProgramMethod(serv));

            }

            //ArrayOfExpression aof = mbs.getArguments();;
            HashSet set = vd.getParam(mbs);
            ListOfProgramVariable inputPara = vd.arrayOfExpression2ListOfProgVar(mbs.getArguments(),0);
            ProgramVariable[] inputParaArray = inputPara.toArray();

            ArrayOfParameterDeclaration paraDecl = mbs.getProgramMethod(serv).getParameters();

            final HashMap values = vd.getValuesForLocation(set, vd.getProgramPIO(itNode.getNode().sequent()));        


            ListOfProgramVariable paramDeclAsPVList= SLListOfProgramVariable.EMPTY_LIST;

            for(int i=0;i<paraDecl.size();i++){
                ProgramVariable next = (ProgramVariable)paraDecl.getParameterDeclaration(i).getVariableSpecification().getProgramVariable();
                Term val = (Term) values.get(TermFactory.DEFAULT.createVariableTerm(inputParaArray[i]));//TODO
                so.addPara2Value(next, val);
                paramDeclAsPVList =paramDeclAsPVList.append(next); 
            }
            so.setParameter(paramDeclAsPVList);

        }catch(Exception e){
            return;

        }


    }

    public ListOfTerm getConstraints(Term toFind){
        //  Term pvTerm = TermFactory.DEFAULT.createVariableTerm(pv);
        ListOfTerm result =SLListOfTerm.EMPTY_LIST;
        for(IteratorOfTerm it= pc.iterator();it.hasNext();){
            final Term t = it.next();
            OpCollector vis = new OpCollector();
            t.execPostOrder(vis);

            if (vis.contains(toFind.op()))
                result = result.append(t);

            //    System.out.println(vis.);

        }

        return result;

    }



    private void createSymbolicObjectsForNewInstances(ListOfTerm pre) {
        for(IteratorOfTerm it=pre.iterator();it.hasNext();){
            Term next= it.next();

            if(next.op() instanceof AttributeOp){
                Term sub = next.sub(0);

                if(getObject(sub,this.symbolicObjects)==null){
                    //VisualDebugger.print("NEW "+sub);

                    //System.out.println(serv.getJavaInfo().getKeYJavaType(sub.sort()).get);
                    symbolicObjects.add(new SymbolicObject(sub,(ClassType)serv.getJavaInfo().getKeYJavaType(sub.sort()).getJavaType(),this.serv));

                }

            }
        }


    }


    private void createPostState(ListOfTerm pre, ListOfTerm post) {
        VisualDebugger.print("createPostState -----");
        IteratorOfTerm pIt = post.iterator();
        for(IteratorOfTerm it= pre.iterator();it.hasNext();){           
            Term preTerm = it.next();
            Term postTerm = pIt.next();
            //System.out.println(preTerm+":="+postTerm);
            if ( preTerm.op() instanceof AttributeOp){
                final Term sub= preTerm.sub(0);
                final SymbolicObject so = getObject(sub, symbolicObjects);
                if (referenceSort(preTerm.sort()))
                    so.addAssociation(((AttributeOp)preTerm.op()).attribute(), getObject(postTerm,symbolicObjects));
                else if (!((ProgramVariable)((AttributeOp)preTerm.op()).attribute()).isImplicit()  || VisualDebugger.showImpliciteAttr)                       
                    so.addValueTerm((ProgramVariable)((AttributeOp)preTerm.op()).attribute(), postTerm);
            }else if (preTerm.op() instanceof ArrayOp){
                final Term sub= preTerm.sub(0);
                final SymbolicArrayObject sao = (SymbolicArrayObject)getObject(sub, symbolicObjects);
                if (referenceSort(preTerm.sort()))
                    sao.addAssociationFromIndex(preTerm.sub(1), getObject(postTerm,symbolicObjects));
                else 
                    sao.setValueTermForIndex(preTerm.sub(1), postTerm);
            } else if (preTerm.op() instanceof ProgramVariable){
                final ProgramVariable pv = (ProgramVariable) preTerm.op();
                SymbolicObject staticO = getStaticObject((ClassType)pv.getContainerType().getJavaType(), symbolicObjects);
                if (staticO==null){
                    if (!pv.isImplicit()  || VisualDebugger.showImpliciteAttr){
                        staticO =new SymbolicObject((ClassType)pv.getContainerType().getJavaType(),serv);
                        symbolicObjects.add(staticO);
                    }
                }
                
                if (referenceSort(preTerm.sort()))
                    staticO.addAssociation(pv, getObject(postTerm,symbolicObjects));
                else if (!pv.isImplicit()  || VisualDebugger.showImpliciteAttr)                       
                    staticO.addValueTerm(pv, postTerm);
            }

        }


    }




    private boolean referenceSort(Sort s){
        JavaInfo info = serv.getJavaInfo();
        KeYJavaType kjt = info.getKeYJavaType(s);
        // System.out.println("KJT "+kjt);
        if(kjt==null)
            return false;
        if (kjt.getJavaType() instanceof ClassType)
            return true;

        return false;
    }



    private void createEquivalenceClassesAndConstraints(){
        term2class = new HashMap();
        IteratorOfTerm it = ante.iterator();
        while(it.hasNext()){
            EquClass ec = null;
            Term t = it.next();
            collectLocations(t);
            if(t.op() instanceof Equality /*&& !containsImplicitAttr(t)*/){
                if(term2class.containsKey(t.sub(0))){
                    ec = (EquClass) term2class.get(t.sub(0));
                    if(term2class.containsKey(t.sub(1))){
                        ec.add((EquClass) term2class.get(t.sub(1)));
                    }else{
                        ec.add(t.sub(1));
                    }
                }else if(term2class.containsKey(t.sub(1))){
                    ec = (EquClass) term2class.get(t.sub(1));
                    ec.add(t.sub(0));
                }else{
                    ec = new EquClass(t.sub(0), t.sub(1));
                }
                IteratorOfTerm ecIt = ec.getMembers().iterator();
                while(ecIt.hasNext()){
                    term2class.put(ecIt.next(), ec);  
                }
            }

        }
        it = succ.iterator();
        while(it.hasNext()){
            Term t = it.next();
            collectLocations(t);
        }
    }


    public EquClass[] getNonPrimitiveLocationEqvClasses(){
        Object[] oa = (new HashSet(term2class.values())).toArray();
        EquClass[] temp = new EquClass[oa.length];
        int l=0;
        for(int i=0; i<oa.length; i++){
            if(((EquClass) oa[i]).getLocations().size() > 0 &&
                    (!((EquClass) oa[i]).isInt() &&
                            !((EquClass) oa[i]).isBoolean())){
                temp[l++] = (EquClass) oa[i];
            }
        }
        EquClass[] result = new EquClass[l];
        for(int i=0; i<l; i++){
            result[i] = temp[i];
        }
        return result;
    }



    private void collectLocations(Term t){
        if(isLocation(t, serv)){
            getEqvClass(t);
            locations = locations.add(t);
        }
        if(!(t.op() instanceof Modality || t.op() instanceof IUpdateOperator ||
                t.op() instanceof Quantifier)){
            for(int i=0; i<t.arity(); i++){
                collectLocations(t.sub(i));
            }
        }
    }



    private SetOfTerm collectLocations2(Term t){
        SetOfTerm result =SetAsListOfTerm.EMPTY_SET;
        if(isLocation(t, serv)){
            result=result.add(t);

        }
        if(!(t.op() instanceof Modality || t.op() instanceof IUpdateOperator ||
                t.op() instanceof Quantifier)){
            for(int i=0; i<t.arity(); i++){
                result = result.union(collectLocations2(t.sub(i)));
            }
        }
        return result;
    }





    public static boolean isLocation(Term t, Services serv){
        OpCollector oc = new OpCollector();
        t.execPostOrder(oc);
        if(oc.contains(Op.NULL)){
            return false;
        }
        return t.op() instanceof AttributeOp && checkIndices(t, serv) &&
        !((ProgramVariable) 
                ((AttributeOp) t.op()).attribute()).isImplicit() || 
                t.op() instanceof ProgramVariable && 
                !((ProgramVariable) t.op()).isImplicit() ||
                t.op() instanceof ArrayOp && checkIndices(t, serv) ||
                t.op() instanceof RigidFunction && t.arity()==0 &&
                !"#".equals(t.op().name().toString()) &&
                !"TRUE".equals(t.op().name().toString()) &&
                !"FALSE".equals(t.op().name().toString()) &&
                t.op().name().toString().indexOf("undef(")==-1;
    }

    private EquClass getEqvClass(Term t){
        if(!term2class.containsKey(t)){
            term2class.put(t, new EquClass(t));
        }
        return (EquClass) term2class.get(t);
    }






    public static boolean checkIndices(Term t, Services serv){
        if(t.op() instanceof AttributeOp){
            return checkIndices(t.sub(0), serv);
        }
        if(t.op() instanceof ArrayOp){
            if(t.sub(1).op().name().toString().equals("Z")){
                if(AbstractMetaOperator.convertToDecimalString(
                        t.sub(1), serv).startsWith("-")){
                    return false;
                }
            }
            return checkIndices(t.sub(0), serv);
        }
        return true;
    }


    private void findDisjointClasses(){
        IteratorOfTerm it = succ.iterator();
        while(it.hasNext()){
            Term t = it.next();
            EquClass e0, e1;
            if(t.op() instanceof Equality /*&&!containsImplicitAttr(t)*/){
                e0 = getEqvClass(t.sub(0));
                e1 = getEqvClass(t.sub(1));
                e0.addDisjoint(t.sub(1));
                e1.addDisjoint(t.sub(0));
            }
        }
    }


    private Set getStaticClasses(Term t){
        Set result = new HashSet();
        if (t.op() instanceof ProgramVariable){            
            if (((ProgramVariable)t.op()).getContainerType()!=null)
                if (!((ProgramVariable)t.op()).isImplicit()  || VisualDebugger.showImpliciteAttr)
                    result.add(((ProgramVariable)t.op()).getContainerType().getJavaType());

        }

        for(int i=0; i<t.arity(); i++){
            result.addAll(getStaticClasses(t.sub(i)));
        }
        return result;


    }

    private Set getStaticClasses(){
        HashSet res = new HashSet();
        for(IteratorOfTerm it = this.pc.iterator();it.hasNext();){
            Term t = it.next();
            res.addAll(this.getStaticClasses(t));

        }

        return res;
    }


    private void  createSymbolicObjects(){
        LinkedList result = new LinkedList();
        EquClass[] npClasses = getNonPrimitiveLocationEqvClasses();
        for(int i=0;i<npClasses.length;i++){
            KeYJavaType t = npClasses[i].getKeYJavaType();
            if (!disjunct(npClasses[i].getMembers(),refInPC)){
                if (npClasses[i].isArray()){
                    SymbolicArrayObject sao = new SymbolicArrayObject(npClasses[i].getMembers(),(ClassType)t.getJavaType(),serv);
                    sao.setPossibleIndexTermConfigurations(getPossibleIndexTerms(npClasses[i].getMembers()));
                    sao.setIndexConfiguration(getPossibleIndexTermsForArray(sao.getTerms(),indexTerms));
                    result.add(sao);
                }
                else
                    result.add(new SymbolicObject(npClasses[i].getMembers(),(ClassType)t.getJavaType(),serv));

            }
        }




        //create static objects
        //System.out.println("Static Type "+);
        for(Iterator it = this.getStaticClasses().iterator();it.hasNext();){
            result.add(new SymbolicObject((ClassType)(it.next()),serv))  ;
        }


        //create self object/ self static class, if not happened
        if (vd.isStaticMethod()){
            final ClassType ct = vd.getType();
            if (this.getStaticObject(ct,result)==null)
                result.add(new SymbolicObject(ct,serv))  ;
        }else{
            final Term self = (Term)vd.getInputPV2term().get((vd.getSelfTerm()));
            if (this.getObject(self, result)==null)
                result.add(new SymbolicObject(self,(ClassType)serv.getJavaInfo().getKeYJavaType(self.sort()).getJavaType(),serv));
        }




        //   create unknown objects
        for(IteratorOfTerm it=postTerms.iterator();it.hasNext();){
            Term next = it.next();
            if (this.referenceSort(next.sort())&&!VisualDebugger.containsImplicitAttr(next)){
                if (getObject(next,result)==null){
                    result.add(new SymbolicObject(next,(ClassType)serv.getJavaInfo().getKeYJavaType(next.sort()).getJavaType(),serv,true));
                }


            }


        }




        // Compute Associations...
        Iterator it = result.iterator();
        while(it.hasNext()){
            SymbolicObject so = (SymbolicObject) it.next();
            IteratorOfTerm it2 =so.getTerms().iterator();
            //SetOfTerm result;
            //          System.out.println("adding assos");
            while(it2.hasNext()){

                Term t = it2.next();
//              System.out.println("ref" +t);

                if (t.op() instanceof AttributeOp){
                    Term sub=t.sub(0);
                    AttributeOp op = (AttributeOp)t.op();
//                  System.out.println("addRef ");
//                  System.out.println(op.attribute());
                    //System.out.println(op.convertToProgram(t, l));
                    //System.out.println(op.referencePrefix(t));
//                  System.out.println(sub);
                    if (refInPC.contains(t)|| postTerms.contains(t)) //TODO ???//only assoc that are in the pc 
                        addReference(op, sub, so, result);
                } else if (t.op() instanceof ArrayOp){
//                  System.out.println("Arrayop");
//                  System.out.println(t.sub(0));
//                  System.out.println(t.sub(1));
                    if (refInPC.contains(t)|| postTerms.contains(t)) //TODO??
                        addIndexReference(t.sub(0),t.sub(1),so,result);



                }    else if (t.op() instanceof ProgramVariable){
                    if (refInPC.contains(t)|| postTerms.contains(t)) //TODO ???//only assoc that are in the pc 
                        addStaticReference((ProgramVariable)t.op(),  so, result);


                }


            }
        }

        //VisualDebugger.print("Collection prim Attributes in "+pc);
        for(IteratorOfTerm it2=pc.iterator();it2.hasNext();){
            Term currentTerm = it2.next();
            SetOfTerm locs = collectLocations2(currentTerm);


            for(IteratorOfTerm it3=locs.iterator();it3.hasNext();){

                Term t2 = it3.next();
                if (!referenceSort(t2.sort())){
                    //       System.out.println("no ref sort"+t2);
                    if (t2.op() instanceof AttributeOp){
                        addAttribute(result,(AttributeOp)t2.op(),t2.sub(0),currentTerm);
                    } else if (t2.op() instanceof ArrayOp){
                        //if (isInt(t2))
                        this.addArrayEntry(result,t2.sub(0),t2.sub(1),currentTerm);
                    } else if (t2.op() instanceof ProgramVariable){
                        ProgramVariable pv = (ProgramVariable) t2.op();
                        KeYJavaType kjt = pv.getContainerType();
                        if (kjt!=null){
                            ClassType ct = (ClassType)kjt.getJavaType();
                            this.addStaticAttribute(result, pv, ct, currentTerm);


                        }


                    }

                }



            }



            // attResult = attResult.union(collectLocations2(t));


        }
        //System.out.println(attResult);




        setInstanceNames(result);
        symbolicObjects= result;
    }


    private LinkedList getPossibleIndexTerms(SetOfTerm members){
        LinkedList result = new LinkedList();
        if (possibleIndexTerms!=null)
            for(int i =0; i< possibleIndexTerms.length; i++){
                SetOfTerm currentIndexTerms = possibleIndexTerms[i];
                SetOfTerm locInd=SetAsListOfTerm.EMPTY_SET;
                SetOfTerm res = SetAsListOfTerm.EMPTY_SET;

                for(IteratorOfTerm locIt=this.arrayLocations.iterator();locIt.hasNext();){
                    Term t = locIt.next();
                    if (members.contains(t.sub(0))){
                        locInd = locInd.add(t.sub(1));
                    }
                }


                for(IteratorOfTerm posIndexTermsIt=currentIndexTerms.iterator();posIndexTermsIt.hasNext();){
                    final Term t = posIndexTermsIt.next();
                    final Term t2 ;
                    if (t.op()==Op.NOT) 
                        t2= t.sub(0);
                    else t2=t;
                    if (locInd.contains(t2.sub(0))&& locInd.contains(t2.sub(1)))
                        res=res.add(t);
                }           
                result.add(res);
            }
        //VisualDebugger.print("POS INDEX TERMS "+result);
        return result;

    }



    private SetOfTerm getPossibleIndexTermsForArray(SetOfTerm members, SetOfTerm ic){
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;

        SetOfTerm currentIndexTerms = ic;
        SetOfTerm locInd=SetAsListOfTerm.EMPTY_SET;
        for(IteratorOfTerm locIt=this.arrayLocations.iterator();locIt.hasNext();){
            Term t = locIt.next();
            if (members.contains(t.sub(0))){
                locInd = locInd.add(t.sub(1));
            }
        }


        for(IteratorOfTerm posIndexTermsIt=currentIndexTerms.iterator();posIndexTermsIt.hasNext();){
            final Term t = posIndexTermsIt.next();
            final Term t2 ;
            if (t.op()==Op.NOT) 
                t2= t.sub(0);
            else t2=t;
            if (locInd.contains(t2.sub(0))&& locInd.contains(t2.sub(1)))
                result=result.add(t);
        }           
        //result=(res);

        //VisualDebugger.print("Index terms for member"+ members+"   :"+result);
        return result;

    }


    public LinkedList getSymbolicObjects(){
        return symbolicObjects;
    }



    private boolean disjunct(SetOfTerm s1, SetOfTerm s2){
        for(IteratorOfTerm it=s1.iterator();it.hasNext();){
            if(s2.contains(it.next()))
                return false;
        }
        return true;
    }



    private void addAttribute(LinkedList objects, AttributeOp op, Term sub, Term cTerm){
        Iterator it = objects.iterator();
        while(it.hasNext()){
            SymbolicObject so = (SymbolicObject) it.next();
            if (so.getTerms().contains(sub)){
                if (!((ProgramVariable)op.attribute()).isImplicit()  || VisualDebugger.showImpliciteAttr)
                    so.addAttributeConstraint((ProgramVariable)op.attribute(), cTerm);
            }
        }

    }

    private void addStaticAttribute(LinkedList objects,ProgramVariable pv,ClassType ct,  Term cTerm){
        Iterator it = objects.iterator();
        while(it.hasNext()){
            SymbolicObject so = (SymbolicObject) it.next();
            if (so.isStatic()&& so.getType().equals(ct)){
                if (!pv.isImplicit()  || VisualDebugger.showImpliciteAttr)
                    so.addAttributeConstraint(pv, cTerm);
            }
        }

    }



    private void addArrayEntry(LinkedList objects, Term  ref, Term index, Term con){
        final Iterator it = objects.iterator();
        while(it.hasNext()){
            SymbolicObject so = (SymbolicObject) it.next();
            if (so.getTerms().contains(ref)) {                
                ( (SymbolicArrayObject)so).addIndexConstraint(index  , con);                
            }
        }

    }

    private void addReference(AttributeOp op, Term sub, SymbolicObject soReferenced, LinkedList objects){
        Iterator  it = objects.iterator();
        while(it.hasNext()){
            SymbolicObject so = (SymbolicObject)it.next();
            if (so.getTerms().contains(sub)){
                if (op.attribute() instanceof  ProgramVariable)
                    so.addAssociation((ProgramVariable)op.attribute(), soReferenced);
                else System.err.println("op.attribute not instance of ProgramVariable");
            }
        }
    }


    private void addStaticReference(ProgramVariable op,  SymbolicObject soReferenced, LinkedList objects){
        Iterator  it = objects.iterator();
        while(it.hasNext()){
            SymbolicObject so = (SymbolicObject)it.next();
            if (so.isStatic()&&so.getType().equals(op.getContainerType().getJavaType()))
                so.addAssociation(op, soReferenced);

        }

    }



    private void addIndexReference(Term sub, Term index, SymbolicObject soReferenced, LinkedList objects){
        Iterator  it = objects.iterator();
        while(it.hasNext()){
            SymbolicObject so = (SymbolicObject)it.next();
            if (so.getTerms().contains(sub)){
                ((SymbolicArrayObject)so).addAssociationFromIndex(index, soReferenced);   
            }
        }
    }

    private SymbolicObject getObject(Term sub, LinkedList objects){
        Iterator  it = objects.iterator();
        while(it.hasNext()){
            final SymbolicObject so = (SymbolicObject)it.next();
            if (so.getTerms().contains(sub)){
                return so;
            }
        }
        return null;
    }


    private SymbolicObject getStaticObject(ClassType ct, LinkedList objects){
        final Iterator  it = objects.iterator();
        while(it.hasNext()){
            final SymbolicObject so = (SymbolicObject)it.next();
            if (so.isStatic()&&so.getType().equals(ct))
                return so;
        }
        return null;
    }

    private int getSerialNumber(SetOfTerm refs){
        int current =-1;

        for(IteratorOfTerm it=refs.iterator();it.hasNext();){
            final Term t = it.next();
            if(ref2ser.containsKey(t)&& 
                    ((current==-1) ||((Integer) ref2ser.get(t)).intValue()<current)){
                current = ((Integer) ref2ser.get(t)).intValue();
            }
        }

        return current;
    }


    private void sort(SymbolicObject a[]) {

        int n = a.length;
        SymbolicObject temp; 

        for (int i=0; i < n-1; i=i+1)          
            for (int j=n-1; j > i; j=j-1)        
                if (a[j-1].getId() > a[j].getId())                 
                {
                    temp = a[j-1];                
                    a[j-1] = a[j];                
                    a[j] = temp;                   
                }
    } 



    private void setInstanceNames(LinkedList objects){
        objects = filterStaticObjects(objects);
        ref2ser = new HashMap();
        ITNode n = this.itNode;
        while(n.getParent()!=null){
            HashMapFromPosInOccurrenceToLabel labels = n.getNode().getNodeInfo().getVisualDebuggerState().getLabels();
            ListOfTerm pc2 = getPc(labels);
            SetOfTerm refs=getReferences(pc2);
            for(IteratorOfTerm it=refs.iterator();it.hasNext();){
                Term t = it.next();
                ref2ser.put(t, new Integer(n.getId()));

            }
            n = n.getParent();
        }


        //references in post term
        int j=0;
        if (postTerms!=null)
            for(IteratorOfTerm it=postTerms.iterator();it.hasNext();){

                Term t = it.next();
//              System.out.println("pt "+t);
                if (referenceSort(t.sort())){
                    if (!ref2ser.containsKey(t)){
                        j++;
                        ref2ser.put(t, new Integer(itNode.getId()+j));

                    }
                }

            }



        VisualDebugger.print("HashMap for Instance Names");

        if (!vd.isStaticMethod())
            ref2ser.put(vd.getInputPV2term().get(TermFactory.DEFAULT.createVariableTerm(vd.getSelfPV())), new Integer(1));



        VisualDebugger.print(ref2ser);

        //System.out.println("INPUT VALUES"+inputVal);

        Iterator it2 = objects.iterator();
        while(it2.hasNext()){
            SymbolicObject so = (SymbolicObject) it2.next();
            so.setId(getSerialNumber(so.getTerms()));
        }


        SymbolicObject[] sos = 
            (SymbolicObject[]) objects.toArray(new SymbolicObject[objects.size()]);

        //sort symbolic objects according to their ids
        sort(sos);




        HashMap counters = new HashMap();

        for(int i =0;i<sos.length;i++){
            SymbolicObject so = sos[i];

            if (so.getId()==-1)
                continue;

            Integer newValue;
            if (counters.containsKey(so.getType())){
                Integer value = (Integer)counters.get(so.getType());
                newValue = new Integer(value.intValue()+1);
                counters.remove(so.getType());
                counters.put(so.getType(), newValue);
            }else{
                newValue = new Integer(0);
                counters.put(so.getType(), newValue);


            }

//          instanceName+=newValue.intValue();

//so.setName(instanceName);


            so.setId(newValue.intValue());


        }



    }



    private LinkedList filterStaticObjects(LinkedList objects) {
        LinkedList result = new LinkedList();
        Iterator it = objects.iterator();
        while(it.hasNext()){
            final SymbolicObject so = (SymbolicObject) it.next();
            if (!so.isStatic())
                result.add(so);
        }
        return result;
    }



    //TODO duplicate in prooflistener

    private ListOfTerm getPc(HashMapFromPosInOccurrenceToLabel labels ){
        IteratorOfPosInOccurrence pioIt = labels.keyIterator();
        ListOfTerm pc2 = SLListOfTerm.EMPTY_LIST;

        while(pioIt.hasNext()){                
            PosInOccurrence pio = pioIt.next();
            //    PCLabel pcLabel = ((PCLabel)labels.get(pio));
            if (!containsJavaBlock(pio.constrainedFormula().formula())){
                Term t = pio.constrainedFormula().formula();
                if (pio.isInAntec())
                    pc2=pc2.append(t);
                else{
                    if (t.op()==Op.NOT){
                        pc2=pc2.append(t.sub(0));
                    }else
                        pc2=pc2.append(TermFactory.DEFAULT.createJunctorTermAndSimplify(Op.NOT,t));
                }

                //  pc = pc.append(pio.constrainedFormula().formula());
            }

        }
        return pc2;
    }



    //TODO duplicate in statevisualization
    private SetOfTerm getReferences(ListOfTerm terms){
        //ListOfTerm pc = itNode.getPc();
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        for(IteratorOfTerm it= terms.iterator();it.hasNext();){
            result = result.union(getReferences2(it.next()));
        }
        return result;
    }

    private SetOfTerm getReferences2(Term t){
        //System.out.println(t);
        // if (t.sort()!= Sort.FORMULA && !this.isBool(t)&&!this.isInt(t))

        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        if (referenceSort(t.sort()))
            result =result.add(t);        
        for(int i=0; i<t.arity(); i++){
            result = result.union(getReferences2(t.sub(i)));
        }
        return result;
    }


    private boolean containsJavaBlock(Term t) {
        boolean result = false;
        if   (t.toString().toUpperCase().equals("POST"))
            return true; //TODO
        if (t.javaBlock() != JavaBlock.EMPTY_JAVABLOCK){
            return true;
        }
        for (int i = 0; i < t.arity(); i++) {
            if (containsJavaBlock(t.sub(i)))
                result = true;
        }
        return result;
    }





    private class EquClass{
        private SetOfTerm disjointRep = SetAsListOfTerm.EMPTY_SET;
        private SetOfTerm members;

        public EquClass(SetOfTerm members){
            this.members = members;          
        }

        public EquClass(Term t){
            this(SetAsListOfTerm.EMPTY_SET.add(t));
        }

        public EquClass(Term t1, Term t2){
            this(SetAsListOfTerm.EMPTY_SET.add(t1).add(t2));
        }

        public void add(Term t){
            members = members.add(t);
        }

        public SetOfTerm getMembers(){
            return members;
        }

        public void add(EquClass ec){
            members = members.union(ec.getMembers());
        }

        public String toString(){
            return "EquClass: ("+ members+")  Disjoint + "+ this.disjointRep+" /";
        }

        public boolean equals(Object o){
            if(!(o instanceof EquClass)){
                return false;
            }
            EquClass eqc = (EquClass) o;
            if(eqc.members.size() != members.size()){
                return false;
            }
            IteratorOfTerm it = members.iterator();
            l:while(it.hasNext()){
                IteratorOfTerm it2 = eqc.members.iterator();
                Term t = it.next();
                while(it2.hasNext()){
                    if(t.toString().equals(it2.next().toString())){
                        continue l;
                    }
                }
                return false;
            }
            return true;
        }


        private boolean isInt(Sort s) {
            return s.extendsTrans(serv.getTypeConverter().getIntegerLDT().targetSort());
        }

        private boolean isArraySort(Sort s){

            return (s instanceof ArraySort);
        }

        public boolean isInt(){
            for(IteratorOfTerm it = members.iterator(); it.hasNext(); ){
                Term t = it.next();
                return isInt(t.sort());                            
            }
            return false;
        }

        public boolean isArray(){
            for(IteratorOfTerm it = members.iterator(); it.hasNext(); ){
                Term t = it.next();              
                return isArraySort(t.sort());                            
            }
            return false;
        }

        public boolean isBoolean(){
            for(IteratorOfTerm it = members.iterator(); it.hasNext(); ){
                if( serv.getTypeConverter().getBooleanLDT().targetSort() == it.next().sort() ){
                    return true;
                }
            }
            return false;
        }

        /**
         * Returns the locations that are members of this equivalence class.
         */
        public SetOfTerm getLocations(){
            SetOfTerm locations = SetAsListOfTerm.EMPTY_SET;
            IteratorOfTerm it = members.iterator();
            while(it.hasNext()){
                Term t = it.next();
                if(ModelGenerator.isLocation(t, serv)){
                    locations = locations.add(t);
                }
            }
            return locations;
        }

        public void addDisjoint(Term t){
            disjointRep = disjointRep.add(t);
        }

        public SetOfTerm getDisjoints(){
            return disjointRep;
        }

        public KeYJavaType getKeYJavaType(){
            IteratorOfTerm it = members.iterator();
            Sort s = it.next().sort();
            while(it.hasNext()){
                Sort s1=it.next().sort();
                if(s1.extendsTrans(s)){
                    s=s1;
                }
            }
            KeYJavaType result = serv.getJavaInfo().getKeYJavaType(s); 
            if (result == null && isInt(s)) {
                result = serv.getJavaInfo().
                getKeYJavaType(serv.getTypeConverter().getIntLDT().targetSort());
            }
            return result;
        }

    }

    public SetOfTerm getIndexTerms() {
        return indexTerms;
    }
}
